import NetHack.Soko22Hazard87.AndIntroBlocks0044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro11250 (p : Pattern) (ha : d76898 p = 1) (hb : d92314 p = 1) : d93495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76893 q = 1) (hb : d92314 q = 1) : d93490 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76893, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76893, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11249 q ha hb
  have h2 (q : Pattern) (ha : d76894 q = 1) (hb : d92314 q = 1) : d93491 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76894, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76894, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76895 q = 1) (hb : d92314 q = 1) : d93492 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76895, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76895, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76896 q = 1) (hb : d92314 q = 1) : d93493 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76896, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76896, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76897 q = 1) (hb : d92314 q = 1) : d93494 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76897, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76897, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76898 q = 1) (hb : d92314 q = 1) : d93495 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76898, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76898, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11251 (p : Pattern) (ha : d769 p = 1) (hb : d92313 p = 1) : d8576 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d761 q = 1) : d761 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d765 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d766 q = 1) (hb : d92313 q = 1) : d6875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d767 q = 1) (hb : d92313 q = 1) : d767 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d768 q = 1) (hb : d92313 q = 1) : d8575 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d768, d8575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d768, d8575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d769 q = 1) (hb : d92313 q = 1) : d8576 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d769, d8576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d769, d8576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11252 (p : Pattern) (ha : d6118 p = 1) (hb : d92314 p = 1) : d8641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d92313 q = 1) : d8577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11251 q ha hb
    | true =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d92314 q = 1) : d8640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6118 q = 1) (hb : d92314 q = 1) : d8641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6118, d8641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6118, d8641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11253 (p : Pattern) (ha : d6124 p = 1) (hb : d92314 p = 1) : d93502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92314 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6119 q = 1) (hb : d92314 q = 1) : d93497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11252 q ha hb
    | true =>
      simp only [d6119, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6120 q = 1) (hb : d92314 q = 1) : d93498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6121 q = 1) (hb : d92314 q = 1) : d93499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6121, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6122 q = 1) (hb : d92314 q = 1) : d93500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6123 q = 1) (hb : d92314 q = 1) : d93501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6124 q = 1) (hb : d92314 q = 1) : d93502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11254 (p : Pattern) (ha : d6127 p = 1) (hb : d92314 p = 1) : d8663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d92313 q = 1) : d8577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11251 q ha hb
    | true =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6115 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d92314 q = 1) : d8640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d8640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6127 q = 1) (hb : d92314 q = 1) : d8663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6127, d8663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6127, d8663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11255 (p : Pattern) (ha : d6133 p = 1) (hb : d92314 p = 1) : d93510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92314 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6119 q = 1) (hb : d92314 q = 1) : d93497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11252 q ha hb
    | true =>
      simp only [d6119, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6120 q = 1) (hb : d92314 q = 1) : d93498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6121 q = 1) (hb : d92314 q = 1) : d93499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6121, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6122 q = 1) (hb : d92314 q = 1) : d93500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6123 q = 1) (hb : d92314 q = 1) : d93501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d92314 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6128 q = 1) (hb : d92314 q = 1) : d93505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11254 q ha hb
    | true =>
      simp only [d6128, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6129 q = 1) (hb : d92314 q = 1) : d93506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6129, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6130 q = 1) (hb : d92314 q = 1) : d93507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6130, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6131 q = 1) (hb : d92314 q = 1) : d93508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6132 q = 1) (hb : d92314 q = 1) : d93509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6133 q = 1) (hb : d92314 q = 1) : d93510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6133, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro11256 (p : Pattern) (ha : d4919 p = 1) (hb : d92313 p = 1) : d6877 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d761 q = 1) : d761 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d765 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d766 q = 1) (hb : d92313 q = 1) : d6875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d4917 q = 1) (hb : d92313 q = 1) : d4917 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4918 q = 1) (hb : d92313 q = 1) : d6876 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d4918, d6876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4918, d6876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4919 q = 1) (hb : d92313 q = 1) : d6877 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d4919, d6877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4919, d6877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11257 (p : Pattern) (ha : d4925 p = 1) (hb : d92314 p = 1) : d93533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4920 q = 1) (hb : d92313 q = 1) : d6878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11256 q ha hb
    | true =>
      simp only [d4920, d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4921 q = 1) (hb : d92313 q = 1) : d6879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4921, d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4922 q = 1) (hb : d92314 q = 1) : d93530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4922, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4923 q = 1) (hb : d92314 q = 1) : d93531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4923, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4924 q = 1) (hb : d92314 q = 1) : d93532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4924, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4925 q = 1) (hb : d92314 q = 1) : d93533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4925, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4925, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11258 (p : Pattern) (ha : d6193 p = 1) (hb : d92314 p = 1) : d93563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92314 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6188 q = 1) (hb : d92314 q = 1) : d93558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6188, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11257 q ha hb
    | true =>
      simp only [d6188, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6189 q = 1) (hb : d92314 q = 1) : d93559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6189, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6189, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6190 q = 1) (hb : d92314 q = 1) : d93560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6190, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6190, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6191 q = 1) (hb : d92314 q = 1) : d93561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6191, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6191, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6192 q = 1) (hb : d92314 q = 1) : d93562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6192, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6192, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d92314 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6193 q = 1) (hb : d92314 q = 1) : d93563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6193, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6193, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11259 (p : Pattern) (ha : d6138 p = 1) (hb : d92314 p = 1) : d93515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d92313 q = 1) : d8577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11251 q ha hb
    | true =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6137 q = 1) (hb : d92314 q = 1) : d93514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6137, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6137, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6138 q = 1) (hb : d92314 q = 1) : d93515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6138, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6138, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11260 (p : Pattern) (ha : d6145 p = 1) (hb : d92314 p = 1) : d93522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d92313 q = 1) : d8577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11251 q ha hb
    | true =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6143 q = 1) (hb : d92314 q = 1) : d93520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6143, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6143, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6144 q = 1) (hb : d92314 q = 1) : d93521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6144, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6144, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6145 q = 1) (hb : d92314 q = 1) : d93522 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6145, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6145, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11261 (p : Pattern) (ha : d845 p = 1) (hb : d92313 p = 1) : d8615 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d842 q = 1) : d842 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d843 q = 1) (hb : d92313 q = 1) : d8613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d92313, d8613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d843, d92313, d8613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d761 q = 1) : d761 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d765 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d766 q = 1) (hb : d92313 q = 1) : d6875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d844 q = 1) (hb : d92313 q = 1) : d8614 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d844, d8614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d844, d8614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d845 q = 1) (hb : d92313 q = 1) : d8615 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d845, d8615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d845, d8615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11262 (p : Pattern) (ha : d6152 p = 1) (hb : d92314 p = 1) : d93529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d846 q = 1) (hb : d92313 q = 1) : d8616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d8616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11261 q ha hb
    | true =>
      simp only [d846, d8616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d847 q = 1) (hb : d92313 q = 1) : d8617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d8617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d847, d8617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6149 q = 1) (hb : d92314 q = 1) : d93526 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6149, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6149, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6150 q = 1) (hb : d92314 q = 1) : d93527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6150, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6150, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6151 q = 1) (hb : d92314 q = 1) : d93528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6151, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6151, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6152 q = 1) (hb : d92314 q = 1) : d93529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6152, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6152, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11263 (p : Pattern) (ha : d76904 p = 1) (hb : d92314 p = 1) : d93539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92314 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6139 q = 1) (hb : d92314 q = 1) : d93516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11259 q ha hb
    | true =>
      simp only [d6139, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6140 q = 1) (hb : d92314 q = 1) : d93517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6141 q = 1) (hb : d92314 q = 1) : d93518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6141, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6142 q = 1) (hb : d92314 q = 1) : d93519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92314 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6146 q = 1) (hb : d92314 q = 1) : d93523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11260 q ha hb
    | true =>
      simp only [d6146, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6147 q = 1) (hb : d92314 q = 1) : d93524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6148 q = 1) (hb : d92314 q = 1) : d93525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6148, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6153 q = 1) (hb : d92314 q = 1) : d93534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11262 q ha hb
    | true =>
      simp only [d6153, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11257 q ha hb
  have h11 (q : Pattern) (ha : d76900 q = 1) (hb : d92314 q = 1) : d93535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76900, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6160 q = 1) (hb : d92314 q = 1) : d8642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11252 q ha hb
    | true =>
      simp only [d6160, d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6161 q = 1) (hb : d92314 q = 1) : d8643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6161, d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76901 q = 1) (hb : d92314 q = 1) : d93536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76901, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76902 q = 1) (hb : d92314 q = 1) : d93537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76902, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76903 q = 1) (hb : d92314 q = 1) : d93538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76903, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76904 q = 1) (hb : d92314 q = 1) : d93539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76904, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76904, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11264 (p : Pattern) (ha : d6166 p = 1) (hb : d92314 p = 1) : d93540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d92313 q = 1) : d8577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11251 q ha hb
    | true =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d92314 q = 1) : d8639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d8639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6137 q = 1) (hb : d92314 q = 1) : d93514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6137, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6137, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6166 q = 1) (hb : d92314 q = 1) : d93540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6166, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6166, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11265 (p : Pattern) (ha : d6171 p = 1) (hb : d92314 p = 1) : d93545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d92313 q = 1) : d8577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11251 q ha hb
    | true =>
      simp only [d770, d8577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d92313 q = 1) : d8578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d8578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d92314 q = 1) : d8638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d92314, d8638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6143 q = 1) (hb : d92314 q = 1) : d93520 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6143, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6143, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6144 q = 1) (hb : d92314 q = 1) : d93521 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6144, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6144, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6171 q = 1) (hb : d92314 q = 1) : d93545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6171, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6171, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11266 (p : Pattern) (ha : d6175 p = 1) (hb : d92314 p = 1) : d93549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d92313 q = 1) : d8616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d8616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11261 q ha hb
    | true =>
      simp only [d846, d8616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d92313 q = 1) : d8617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d8617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d8617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6149 q = 1) (hb : d92314 q = 1) : d93526 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6149, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6149, d92314, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6150 q = 1) (hb : d92314 q = 1) : d93527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6150, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6150, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6151 q = 1) (hb : d92314 q = 1) : d93528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6151, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6151, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6175 q = 1) (hb : d92314 q = 1) : d93549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6175, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6175, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11267 (p : Pattern) (ha : d6176 p = 1) (hb : d92314 p = 1) : d93550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d92313 q = 1) : d6878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11256 q ha hb
    | true =>
      simp only [d4920, d6878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d92313 q = 1) : d6879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d6879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4922 q = 1) (hb : d92314 q = 1) : d93530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4922, d92314, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4923 q = 1) (hb : d92314 q = 1) : d93531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4923, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4924 q = 1) (hb : d92314 q = 1) : d93532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4924, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6176 q = 1) (hb : d92314 q = 1) : d93550 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6176, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6176, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11268 (p : Pattern) (ha : d76909 p = 1) (hb : d92314 p = 1) : d93556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92314 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6139 q = 1) (hb : d92314 q = 1) : d93516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11259 q ha hb
    | true =>
      simp only [d6139, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6140 q = 1) (hb : d92314 q = 1) : d93517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6141 q = 1) (hb : d92314 q = 1) : d93518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6141, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6142 q = 1) (hb : d92314 q = 1) : d93519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92314 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6146 q = 1) (hb : d92314 q = 1) : d93523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11260 q ha hb
    | true =>
      simp only [d6146, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6147 q = 1) (hb : d92314 q = 1) : d93524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6148 q = 1) (hb : d92314 q = 1) : d93525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6148, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6153 q = 1) (hb : d92314 q = 1) : d93534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11262 q ha hb
    | true =>
      simp only [d6153, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11257 q ha hb
  have h11 (q : Pattern) (ha : d76900 q = 1) (hb : d92314 q = 1) : d93535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76900, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6160 q = 1) (hb : d92314 q = 1) : d8642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11252 q ha hb
    | true =>
      simp only [d6160, d8642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6161 q = 1) (hb : d92314 q = 1) : d8643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6161, d8643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76901 q = 1) (hb : d92314 q = 1) : d93536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76901, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76902 q = 1) (hb : d92314 q = 1) : d93537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76902, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76903 q = 1) (hb : d92314 q = 1) : d93538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76903, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d916 q = 1) (hb : d92314 q = 1) : d916 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6167 q = 1) (hb : d92314 q = 1) : d93541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6167, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11264 q ha hb
    | true =>
      simp only [d6167, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6168 q = 1) (hb : d92314 q = 1) : d93542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6168, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6168, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6169 q = 1) (hb : d92314 q = 1) : d93543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6169, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6169, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6170 q = 1) (hb : d92314 q = 1) : d93544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6170, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6170, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d922 q = 1) (hb : d92314 q = 1) : d922 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6172 q = 1) (hb : d92314 q = 1) : d93546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6172, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11265 q ha hb
    | true =>
      simp only [d6172, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6173 q = 1) (hb : d92314 q = 1) : d93547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6173, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6173, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6174 q = 1) (hb : d92314 q = 1) : d93548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6174, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6174, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6177 q = 1) (hb : d92314 q = 1) : d93551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11266 q ha hb
    | true =>
      simp only [d6177, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11267 q ha hb
  have h27 (q : Pattern) (ha : d76905 q = 1) (hb : d92314 q = 1) : d93552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76905, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6181 q = 1) (hb : d92314 q = 1) : d8664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11254 q ha hb
    | true =>
      simp only [d6181, d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6182 q = 1) (hb : d92314 q = 1) : d8665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6182, d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76906 q = 1) (hb : d92314 q = 1) : d93553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76906, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76907 q = 1) (hb : d92314 q = 1) : d93554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76907, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76907, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76908 q = 1) (hb : d92314 q = 1) : d93555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76908, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76908, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76909 q = 1) (hb : d92314 q = 1) : d93556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76909, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76909, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11269 (p : Pattern) (ha : d76916 p = 1) (hb : d92314 p = 1) : d93570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6177 q = 1) (hb : d92314 q = 1) : d93551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11266 q ha hb
    | true =>
      simp only [d6177, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11267 q ha hb
  have h2 (q : Pattern) (ha : d76905 q = 1) (hb : d92314 q = 1) : d93552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76905, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6181 q = 1) (hb : d92314 q = 1) : d8664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11254 q ha hb
    | true =>
      simp only [d6181, d8664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6182 q = 1) (hb : d92314 q = 1) : d8665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6182, d8665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76906 q = 1) (hb : d92314 q = 1) : d93553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76906, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76914 q = 1) (hb : d92314 q = 1) : d93568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76914, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76914, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76915 q = 1) (hb : d92314 q = 1) : d93569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76915, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76915, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76916 q = 1) (hb : d92314 q = 1) : d93570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76916, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76916, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11270 (p : Pattern) (ha : d992 p = 1) (hb : d92313 p = 1) : d8691 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d979 q = 1) : d979 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d984 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d985 q = 1) (hb : d92313 q = 1) : d8689 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d92313, d8689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d985, d92313, d8689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d984 q = 1) : d984 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d989 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d990 q = 1) (hb : d92313 q = 1) : d6921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d991 q = 1) (hb : d92313 q = 1) : d8690 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d8690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d991, d8690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d992 q = 1) (hb : d92313 q = 1) : d8691 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d8691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d992, d8691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11271 (p : Pattern) (ha : d6209 p = 1) (hb : d92314 p = 1) : d93579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d92313 q = 1) : d8692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d8692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11270 q ha hb
    | true =>
      simp only [d993, d8692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d92313 q = 1) : d8693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d8693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d8693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6206 q = 1) (hb : d92314 q = 1) : d93576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6206, d92314, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6206, d92314, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6207 q = 1) (hb : d92314 q = 1) : d93577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6207, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6207, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6208 q = 1) (hb : d92314 q = 1) : d93578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6208, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6208, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6209 q = 1) (hb : d92314 q = 1) : d93579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6209, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6209, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11272 (p : Pattern) (ha : d6216 p = 1) (hb : d92313 p = 1) : d6923 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d984 q = 1) : d984 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d990 q = 1) (hb : d92313 q = 1) : d6921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6214 q = 1) (hb : d92313 q = 1) : d6214 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6215 q = 1) (hb : d92313 q = 1) : d6922 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6215, d6922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6215, d6922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6216 q = 1) (hb : d92313 q = 1) : d6923 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6216, d6923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6216, d6923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11273 (p : Pattern) (ha : d6222 p = 1) (hb : d92314 p = 1) : d93583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6217 q = 1) (hb : d92313 q = 1) : d6924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d6924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11272 q ha hb
    | true =>
      simp only [d6217, d6924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6218 q = 1) (hb : d92313 q = 1) : d6925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, d6925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6218, d6925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6219 q = 1) (hb : d92314 q = 1) : d93580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6219, d92314, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6219, d92314, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6220 q = 1) (hb : d92314 q = 1) : d93581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6220, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6220, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6221 q = 1) (hb : d92314 q = 1) : d93582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6221, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6221, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6222 q = 1) (hb : d92314 q = 1) : d93583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6222, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6222, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11274 (p : Pattern) (ha : d997 p = 1) (hb : d92313 p = 1) : d8715 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d984 q = 1) : d984 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d990 q = 1) (hb : d92313 q = 1) : d6921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d995 q = 1) (hb : d92313 q = 1) : d995 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d996 q = 1) (hb : d92313 q = 1) : d8714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d8714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d996, d8714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d997 q = 1) (hb : d92313 q = 1) : d8715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d8715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d997, d8715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11275 (p : Pattern) (ha : d6233 p = 1) (hb : d92314 p = 1) : d8721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d92313 q = 1) : d8716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d8716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11274 q ha hb
    | true =>
      simp only [d998, d8716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d92313 q = 1) : d8717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d8717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d8717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6230 q = 1) (hb : d92314 q = 1) : d8718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, d92314, d8718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6230, d92314, d8718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6231 q = 1) (hb : d92314 q = 1) : d8719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, d8719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6231, d8719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6232 q = 1) (hb : d92314 q = 1) : d8720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, d8720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6232, d8720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6233 q = 1) (hb : d92314 q = 1) : d8721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, d8721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6233, d8721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11276 (p : Pattern) (ha : d76926 p = 1) (hb : d92314 p = 1) : d93589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6223 q = 1) (hb : d92314 q = 1) : d93584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6223, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11271 q ha hb
    | true =>
      simp only [d6223, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11273 q ha hb
  have h2 (q : Pattern) (ha : d76922 q = 1) (hb : d92314 q = 1) : d93585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76922, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76922, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6234 q = 1) (hb : d92314 q = 1) : d8722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d8722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11275 q ha hb
    | true =>
      simp only [d6234, d8722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6235 q = 1) (hb : d92314 q = 1) : d8723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d8723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6235, d8723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76923 q = 1) (hb : d92314 q = 1) : d93586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76923, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76923, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76924 q = 1) (hb : d92314 q = 1) : d93587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76924, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76924, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76925 q = 1) (hb : d92314 q = 1) : d93588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76925, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76925, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76926 q = 1) (hb : d92314 q = 1) : d93589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76926, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76926, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11277 (p : Pattern) (ha : d76932 p = 1) (hb : d92314 p = 1) : d93595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6125 q = 1) (hb : d92314 q = 1) : d93503 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6125, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6125, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11253 q ha hb
  have h2 (q : Pattern) (ha : d6126 q = 1) (hb : d92314 q = 1) : d93504 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6126, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6126, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6134 q = 1) (hb : d92314 q = 1) : d93511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11253 q ha hb
    | true =>
      simp only [d6134, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11255 q ha hb
  have h4 (q : Pattern) (ha : d6135 q = 1) (hb : d92314 q = 1) : d93512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6135, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6136 q = 1) (hb : d92314 q = 1) : d93513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6136, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6136, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76910 q = 1) (hb : d92314 q = 1) : d93557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76910, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11263 q ha hb
    | true =>
      simp only [d76910, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11268 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d92314 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6194 q = 1) (hb : d92314 q = 1) : d93564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6194, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11258 q ha hb
    | true =>
      simp only [d6194, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76911 q = 1) (hb : d92314 q = 1) : d93565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76911, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76911, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76912 q = 1) (hb : d92314 q = 1) : d93566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76912, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76912, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76913 q = 1) (hb : d92314 q = 1) : d93567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76913, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76913, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76917 q = 1) (hb : d92314 q = 1) : d93571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76917, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76917, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11269 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d92314 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76918 q = 1) (hb : d92314 q = 1) : d93572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76918, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76918, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76919 q = 1) (hb : d92314 q = 1) : d93573 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76919, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76919, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76920 q = 1) (hb : d92314 q = 1) : d93574 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76920, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76920, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76921 q = 1) (hb : d92314 q = 1) : d93575 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76921, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76921, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76927 q = 1) (hb : d92314 q = 1) : d93590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76927, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76927, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11276 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d92314 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76928 q = 1) (hb : d92314 q = 1) : d93591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76928, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76928, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76929 q = 1) (hb : d92314 q = 1) : d93592 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76929, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76929, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76930 q = 1) (hb : d92314 q = 1) : d93593 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76930, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76930, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76931 q = 1) (hb : d92314 q = 1) : d93594 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76931, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76931, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76932 q = 1) (hb : d92314 q = 1) : d93595 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76932, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76932, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro11278 (p : Pattern) (ha : d76938 p = 1) (hb : d92314 p = 1) : d93601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76933 q = 1) (hb : d92314 q = 1) : d93596 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76933, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76933, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11277 q ha hb
  have h2 (q : Pattern) (ha : d76934 q = 1) (hb : d92314 q = 1) : d93597 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76934, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76934, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76935 q = 1) (hb : d92314 q = 1) : d93598 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76935, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76935, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76936 q = 1) (hb : d92314 q = 1) : d93599 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76936, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76936, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76937 q = 1) (hb : d92314 q = 1) : d93600 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76937, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76937, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76938 q = 1) (hb : d92314 q = 1) : d93601 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76938, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76938, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11279 (p : Pattern) (ha : d1148 p = 1) (hb : d92313 p = 1) : d8743 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1131 q = 1) : d1131 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1145 q = 1) (hb : d92313 q = 1) : d6954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1146 q = 1) (hb : d92313 q = 1) : d1146 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1147 q = 1) (hb : d92313 q = 1) : d8742 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1147, d8742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1147, d8742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1148 q = 1) (hb : d92313 q = 1) : d8743 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1148, d8743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1148, d8743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11280 (p : Pattern) (ha : d6257 p = 1) (hb : d92314 p = 1) : d8808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d92313 q = 1) : d8744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11279 q ha hb
    | true =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d92314 q = 1) : d8807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6257 q = 1) (hb : d92314 q = 1) : d8808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6257, d8808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6257, d8808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11281 (p : Pattern) (ha : d6263 p = 1) (hb : d92314 p = 1) : d93609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92314 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6258 q = 1) (hb : d92314 q = 1) : d93604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11280 q ha hb
    | true =>
      simp only [d6258, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6259 q = 1) (hb : d92314 q = 1) : d93605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6260 q = 1) (hb : d92314 q = 1) : d93606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6260, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6261 q = 1) (hb : d92314 q = 1) : d93607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6262 q = 1) (hb : d92314 q = 1) : d93608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6263 q = 1) (hb : d92314 q = 1) : d93609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11282 (p : Pattern) (ha : d6266 p = 1) (hb : d92314 p = 1) : d8830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d92313 q = 1) : d8744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11279 q ha hb
    | true =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6254 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d92314 q = 1) : d8807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d8807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6266 q = 1) (hb : d92314 q = 1) : d8830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6266, d8830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6266, d8830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11283 (p : Pattern) (ha : d6272 p = 1) (hb : d92314 p = 1) : d93617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92314 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6258 q = 1) (hb : d92314 q = 1) : d93604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11280 q ha hb
    | true =>
      simp only [d6258, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6259 q = 1) (hb : d92314 q = 1) : d93605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6260 q = 1) (hb : d92314 q = 1) : d93606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6260, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6261 q = 1) (hb : d92314 q = 1) : d93607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6262 q = 1) (hb : d92314 q = 1) : d93608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d92314 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6267 q = 1) (hb : d92314 q = 1) : d93612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11282 q ha hb
    | true =>
      simp only [d6267, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6268 q = 1) (hb : d92314 q = 1) : d93613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6268, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6269 q = 1) (hb : d92314 q = 1) : d93614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6269, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6270 q = 1) (hb : d92314 q = 1) : d93615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6271 q = 1) (hb : d92314 q = 1) : d93616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6272 q = 1) (hb : d92314 q = 1) : d93617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6272, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro11284 (p : Pattern) (ha : d5029 p = 1) (hb : d92313 p = 1) : d6956 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1131 q = 1) : d1131 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1145 q = 1) (hb : d92313 q = 1) : d6954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5027 q = 1) (hb : d92313 q = 1) : d5027 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5028 q = 1) (hb : d92313 q = 1) : d6955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5028, d6955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5028, d6955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5029 q = 1) (hb : d92313 q = 1) : d6956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5029, d6956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5029, d6956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11285 (p : Pattern) (ha : d5035 p = 1) (hb : d92314 p = 1) : d93640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5030 q = 1) (hb : d92313 q = 1) : d6957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11284 q ha hb
    | true =>
      simp only [d5030, d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5031 q = 1) (hb : d92313 q = 1) : d6958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5031, d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5032 q = 1) (hb : d92314 q = 1) : d93637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5032, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5033 q = 1) (hb : d92314 q = 1) : d93638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5033, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5034 q = 1) (hb : d92314 q = 1) : d93639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5034, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5035 q = 1) (hb : d92314 q = 1) : d93640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5035, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5035, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11286 (p : Pattern) (ha : d6332 p = 1) (hb : d92314 p = 1) : d93670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92314 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6327 q = 1) (hb : d92314 q = 1) : d93665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6327, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11285 q ha hb
    | true =>
      simp only [d6327, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6328 q = 1) (hb : d92314 q = 1) : d93666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6328, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6328, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6329 q = 1) (hb : d92314 q = 1) : d93667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6329, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6329, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6330 q = 1) (hb : d92314 q = 1) : d93668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6330, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6330, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6331 q = 1) (hb : d92314 q = 1) : d93669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6331, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6331, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d92314 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6332 q = 1) (hb : d92314 q = 1) : d93670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6332, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6332, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11287 (p : Pattern) (ha : d6277 p = 1) (hb : d92314 p = 1) : d93622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d92313 q = 1) : d8744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11279 q ha hb
    | true =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6276 q = 1) (hb : d92314 q = 1) : d93621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6276, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6277 q = 1) (hb : d92314 q = 1) : d93622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6277, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6277, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11288 (p : Pattern) (ha : d6284 p = 1) (hb : d92314 p = 1) : d93629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d92313 q = 1) : d8744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11279 q ha hb
    | true =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6282 q = 1) (hb : d92314 q = 1) : d93627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6282, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6283 q = 1) (hb : d92314 q = 1) : d93628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6283, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6284 q = 1) (hb : d92314 q = 1) : d93629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6284, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6284, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11289 (p : Pattern) (ha : d1221 p = 1) (hb : d92313 p = 1) : d8782 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1218 q = 1) : d1218 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1219 q = 1) (hb : d92313 q = 1) : d8780 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d92313, d8780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1219, d92313, d8780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1131 q = 1) : d1131 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1144 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1145 q = 1) (hb : d92313 q = 1) : d6954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1220 q = 1) (hb : d92313 q = 1) : d8781 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1220, d8781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1220, d8781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1221 q = 1) (hb : d92313 q = 1) : d8782 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1221, d8782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1221, d8782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11290 (p : Pattern) (ha : d6291 p = 1) (hb : d92314 p = 1) : d93636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1222 q = 1) (hb : d92313 q = 1) : d8783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d8783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11289 q ha hb
    | true =>
      simp only [d1222, d8783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1223 q = 1) (hb : d92313 q = 1) : d8784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d8784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1223, d8784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6288 q = 1) (hb : d92314 q = 1) : d93633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6288, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6289 q = 1) (hb : d92314 q = 1) : d93634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6289, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6290 q = 1) (hb : d92314 q = 1) : d93635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6290, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6291 q = 1) (hb : d92314 q = 1) : d93636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6291, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6291, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11291 (p : Pattern) (ha : d76945 p = 1) (hb : d92314 p = 1) : d93646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92314 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6278 q = 1) (hb : d92314 q = 1) : d93623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11287 q ha hb
    | true =>
      simp only [d6278, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6279 q = 1) (hb : d92314 q = 1) : d93624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6280 q = 1) (hb : d92314 q = 1) : d93625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6280, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6281 q = 1) (hb : d92314 q = 1) : d93626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92314 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6285 q = 1) (hb : d92314 q = 1) : d93630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11288 q ha hb
    | true =>
      simp only [d6285, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6286 q = 1) (hb : d92314 q = 1) : d93631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6287 q = 1) (hb : d92314 q = 1) : d93632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6287, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6292 q = 1) (hb : d92314 q = 1) : d93641 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11290 q ha hb
    | true =>
      simp only [d6292, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11285 q ha hb
  have h11 (q : Pattern) (ha : d76941 q = 1) (hb : d92314 q = 1) : d93642 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76941, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6299 q = 1) (hb : d92314 q = 1) : d8809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11280 q ha hb
    | true =>
      simp only [d6299, d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6300 q = 1) (hb : d92314 q = 1) : d8810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6300, d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76942 q = 1) (hb : d92314 q = 1) : d93643 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76942, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76943 q = 1) (hb : d92314 q = 1) : d93644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76943, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76944 q = 1) (hb : d92314 q = 1) : d93645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76944, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76945 q = 1) (hb : d92314 q = 1) : d93646 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76945, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76945, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11292 (p : Pattern) (ha : d6305 p = 1) (hb : d92314 p = 1) : d93647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d92313 q = 1) : d8744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11279 q ha hb
    | true =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d92314 q = 1) : d8806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d8806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6276 q = 1) (hb : d92314 q = 1) : d93621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6276, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6305 q = 1) (hb : d92314 q = 1) : d93647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6305, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6305, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11293 (p : Pattern) (ha : d6310 p = 1) (hb : d92314 p = 1) : d93652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d92313 q = 1) : d8744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11279 q ha hb
    | true =>
      simp only [d1149, d8744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d92313 q = 1) : d8745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d8745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d92314 q = 1) : d8805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d92314, d8805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6282 q = 1) (hb : d92314 q = 1) : d93627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6282, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6283 q = 1) (hb : d92314 q = 1) : d93628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6283, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6310 q = 1) (hb : d92314 q = 1) : d93652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6310, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6310, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11294 (p : Pattern) (ha : d6314 p = 1) (hb : d92314 p = 1) : d93656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d92313 q = 1) : d8783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d8783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11289 q ha hb
    | true =>
      simp only [d1222, d8783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d92313 q = 1) : d8784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d8784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d8784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6288 q = 1) (hb : d92314 q = 1) : d93633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6288, d92314, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6289 q = 1) (hb : d92314 q = 1) : d93634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6289, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6290 q = 1) (hb : d92314 q = 1) : d93635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6290, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6314 q = 1) (hb : d92314 q = 1) : d93656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6314, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6314, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11295 (p : Pattern) (ha : d6315 p = 1) (hb : d92314 p = 1) : d93657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d92313 q = 1) : d6957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11284 q ha hb
    | true =>
      simp only [d5030, d6957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d92313 q = 1) : d6958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d6958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5032 q = 1) (hb : d92314 q = 1) : d93637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5032, d92314, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5033 q = 1) (hb : d92314 q = 1) : d93638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5033, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5034 q = 1) (hb : d92314 q = 1) : d93639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5034, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6315 q = 1) (hb : d92314 q = 1) : d93657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6315, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6315, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11296 (p : Pattern) (ha : d76950 p = 1) (hb : d92314 p = 1) : d93663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92314 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6278 q = 1) (hb : d92314 q = 1) : d93623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11287 q ha hb
    | true =>
      simp only [d6278, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6279 q = 1) (hb : d92314 q = 1) : d93624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6280 q = 1) (hb : d92314 q = 1) : d93625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6280, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6281 q = 1) (hb : d92314 q = 1) : d93626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92314 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6285 q = 1) (hb : d92314 q = 1) : d93630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11288 q ha hb
    | true =>
      simp only [d6285, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6286 q = 1) (hb : d92314 q = 1) : d93631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6287 q = 1) (hb : d92314 q = 1) : d93632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6287, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6292 q = 1) (hb : d92314 q = 1) : d93641 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11290 q ha hb
    | true =>
      simp only [d6292, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11285 q ha hb
  have h11 (q : Pattern) (ha : d76941 q = 1) (hb : d92314 q = 1) : d93642 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76941, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6299 q = 1) (hb : d92314 q = 1) : d8809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11280 q ha hb
    | true =>
      simp only [d6299, d8809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6300 q = 1) (hb : d92314 q = 1) : d8810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6300, d8810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76942 q = 1) (hb : d92314 q = 1) : d93643 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76942, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76943 q = 1) (hb : d92314 q = 1) : d93644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76943, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76944 q = 1) (hb : d92314 q = 1) : d93645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76944, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1327 q = 1) (hb : d92314 q = 1) : d1327 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6306 q = 1) (hb : d92314 q = 1) : d93648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6306, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11292 q ha hb
    | true =>
      simp only [d6306, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6307 q = 1) (hb : d92314 q = 1) : d93649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6307, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6307, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6308 q = 1) (hb : d92314 q = 1) : d93650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6308, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6308, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6309 q = 1) (hb : d92314 q = 1) : d93651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6309, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6309, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1333 q = 1) (hb : d92314 q = 1) : d1333 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6311 q = 1) (hb : d92314 q = 1) : d93653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6311, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11293 q ha hb
    | true =>
      simp only [d6311, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6312 q = 1) (hb : d92314 q = 1) : d93654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6312, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6312, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6313 q = 1) (hb : d92314 q = 1) : d93655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6313, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6313, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6316 q = 1) (hb : d92314 q = 1) : d93658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11294 q ha hb
    | true =>
      simp only [d6316, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11295 q ha hb
  have h27 (q : Pattern) (ha : d76946 q = 1) (hb : d92314 q = 1) : d93659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76946, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6320 q = 1) (hb : d92314 q = 1) : d8831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11282 q ha hb
    | true =>
      simp only [d6320, d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6321 q = 1) (hb : d92314 q = 1) : d8832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6321, d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76947 q = 1) (hb : d92314 q = 1) : d93660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76947, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76948 q = 1) (hb : d92314 q = 1) : d93661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76948, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76948, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76949 q = 1) (hb : d92314 q = 1) : d93662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76949, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76949, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76950 q = 1) (hb : d92314 q = 1) : d93663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76950, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76950, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11297 (p : Pattern) (ha : d76957 p = 1) (hb : d92314 p = 1) : d93677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6316 q = 1) (hb : d92314 q = 1) : d93658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11294 q ha hb
    | true =>
      simp only [d6316, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11295 q ha hb
  have h2 (q : Pattern) (ha : d76946 q = 1) (hb : d92314 q = 1) : d93659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76946, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6320 q = 1) (hb : d92314 q = 1) : d8831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11282 q ha hb
    | true =>
      simp only [d6320, d8831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6321 q = 1) (hb : d92314 q = 1) : d8832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6321, d8832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76947 q = 1) (hb : d92314 q = 1) : d93660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76947, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76955 q = 1) (hb : d92314 q = 1) : d93675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76955, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76955, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76956 q = 1) (hb : d92314 q = 1) : d93676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76956, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76956, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76957 q = 1) (hb : d92314 q = 1) : d93677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76957, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76957, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11298 (p : Pattern) (ha : d1417 p = 1) (hb : d92313 p = 1) : d8858 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1399 q = 1) : d1399 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1405 q = 1) (hb : d92313 q = 1) : d8856 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d92313, d8856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1405, d92313, d8856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1404 q = 1) : d1404 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1414 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1415 q = 1) (hb : d92313 q = 1) : d7000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1416 q = 1) (hb : d92313 q = 1) : d8857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d8857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1416, d8857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1417 q = 1) (hb : d92313 q = 1) : d8858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d8858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1417, d8858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11299 (p : Pattern) (ha : d6348 p = 1) (hb : d92314 p = 1) : d93686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d92313 q = 1) : d8859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d8859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11298 q ha hb
    | true =>
      simp only [d1418, d8859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d92313 q = 1) : d8860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d8860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d8860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6345 q = 1) (hb : d92314 q = 1) : d93683 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6345, d92314, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6345, d92314, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6346 q = 1) (hb : d92314 q = 1) : d93684 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6346, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6346, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6347 q = 1) (hb : d92314 q = 1) : d93685 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6347, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6347, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6348 q = 1) (hb : d92314 q = 1) : d93686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6348, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6348, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11300 (p : Pattern) (ha : d6361 p = 1) (hb : d92313 p = 1) : d7002 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1404 q = 1) : d1404 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1414 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1415 q = 1) (hb : d92313 q = 1) : d7000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6359 q = 1) (hb : d92313 q = 1) : d6359 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6360 q = 1) (hb : d92313 q = 1) : d7001 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6360, d7001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6360, d7001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6361 q = 1) (hb : d92313 q = 1) : d7002 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6361, d7002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6361, d7002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11301 (p : Pattern) (ha : d6367 p = 1) (hb : d92314 p = 1) : d93690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6362 q = 1) (hb : d92313 q = 1) : d7003 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d7003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11300 q ha hb
    | true =>
      simp only [d6362, d7003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6363 q = 1) (hb : d92313 q = 1) : d7004 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, d7004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6363, d7004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6364 q = 1) (hb : d92314 q = 1) : d93687 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6364, d92314, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6364, d92314, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6365 q = 1) (hb : d92314 q = 1) : d93688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6365, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6365, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6366 q = 1) (hb : d92314 q = 1) : d93689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6366, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6366, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6367 q = 1) (hb : d92314 q = 1) : d93690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6367, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6367, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11302 (p : Pattern) (ha : d1422 p = 1) (hb : d92313 p = 1) : d8882 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1404 q = 1) : d1404 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1414 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1415 q = 1) (hb : d92313 q = 1) : d7000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1420 q = 1) (hb : d92313 q = 1) : d1420 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1421 q = 1) (hb : d92313 q = 1) : d8881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d8881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1421, d8881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1422 q = 1) (hb : d92313 q = 1) : d8882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d8882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1422, d8882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11303 (p : Pattern) (ha : d6378 p = 1) (hb : d92314 p = 1) : d8888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d92313 q = 1) : d8883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d8883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11302 q ha hb
    | true =>
      simp only [d1423, d8883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d92313 q = 1) : d8884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d8884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d8884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6375 q = 1) (hb : d92314 q = 1) : d8885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, d92314, d8885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6375, d92314, d8885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6376 q = 1) (hb : d92314 q = 1) : d8886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, d8886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6376, d8886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6377 q = 1) (hb : d92314 q = 1) : d8887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, d8887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6377, d8887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6378 q = 1) (hb : d92314 q = 1) : d8888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, d8888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6378, d8888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11304 (p : Pattern) (ha : d76967 p = 1) (hb : d92314 p = 1) : d93696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6368 q = 1) (hb : d92314 q = 1) : d93691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6368, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11299 q ha hb
    | true =>
      simp only [d6368, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11301 q ha hb
  have h2 (q : Pattern) (ha : d76963 q = 1) (hb : d92314 q = 1) : d93692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76963, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76963, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6379 q = 1) (hb : d92314 q = 1) : d8889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d8889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11303 q ha hb
    | true =>
      simp only [d6379, d8889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6380 q = 1) (hb : d92314 q = 1) : d8890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d8890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6380, d8890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76964 q = 1) (hb : d92314 q = 1) : d93693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76964, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76964, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76965 q = 1) (hb : d92314 q = 1) : d93694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76965, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76965, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76966 q = 1) (hb : d92314 q = 1) : d93695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76966, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76966, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76967 q = 1) (hb : d92314 q = 1) : d93696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76967, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76967, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11305 (p : Pattern) (ha : d76973 p = 1) (hb : d92314 p = 1) : d93702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6264 q = 1) (hb : d92314 q = 1) : d93610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6264, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6264, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11281 q ha hb
  have h2 (q : Pattern) (ha : d6265 q = 1) (hb : d92314 q = 1) : d93611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6265, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6265, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6273 q = 1) (hb : d92314 q = 1) : d93618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11281 q ha hb
    | true =>
      simp only [d6273, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11283 q ha hb
  have h4 (q : Pattern) (ha : d6274 q = 1) (hb : d92314 q = 1) : d93619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6274, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6275 q = 1) (hb : d92314 q = 1) : d93620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6275, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6275, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76951 q = 1) (hb : d92314 q = 1) : d93664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76951, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11291 q ha hb
    | true =>
      simp only [d76951, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11296 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d92314 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6333 q = 1) (hb : d92314 q = 1) : d93671 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6333, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11286 q ha hb
    | true =>
      simp only [d6333, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76952 q = 1) (hb : d92314 q = 1) : d93672 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76952, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76952, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76953 q = 1) (hb : d92314 q = 1) : d93673 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76953, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76953, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76954 q = 1) (hb : d92314 q = 1) : d93674 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76954, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76954, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76958 q = 1) (hb : d92314 q = 1) : d93678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76958, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76958, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11297 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d92314 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76959 q = 1) (hb : d92314 q = 1) : d93679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76959, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76959, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76960 q = 1) (hb : d92314 q = 1) : d93680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76960, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76960, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76961 q = 1) (hb : d92314 q = 1) : d93681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76961, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76961, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76962 q = 1) (hb : d92314 q = 1) : d93682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76962, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76962, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76968 q = 1) (hb : d92314 q = 1) : d93697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76968, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76968, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11304 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d92314 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76969 q = 1) (hb : d92314 q = 1) : d93698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76969, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76969, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76970 q = 1) (hb : d92314 q = 1) : d93699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76970, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76970, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76971 q = 1) (hb : d92314 q = 1) : d93700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76971, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76971, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76972 q = 1) (hb : d92314 q = 1) : d93701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76972, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76972, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76973 q = 1) (hb : d92314 q = 1) : d93702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76973, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76973, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro11306 (p : Pattern) (ha : d76979 p = 1) (hb : d92314 p = 1) : d93708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76974 q = 1) (hb : d92314 q = 1) : d93703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76974, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76974, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11305 q ha hb
  have h2 (q : Pattern) (ha : d76975 q = 1) (hb : d92314 q = 1) : d93704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76975, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76975, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76976 q = 1) (hb : d92314 q = 1) : d93705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76976, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76976, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76977 q = 1) (hb : d92314 q = 1) : d93706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76977, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76977, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76978 q = 1) (hb : d92314 q = 1) : d93707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76978, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76978, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76979 q = 1) (hb : d92314 q = 1) : d93708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76979, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76979, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11307 (p : Pattern) (ha : d1609 p = 1) (hb : d92313 p = 1) : d8911 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1592 q = 1) : d1592 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1606 q = 1) (hb : d92313 q = 1) : d7034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1607 q = 1) (hb : d92313 q = 1) : d1607 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1608 q = 1) (hb : d92313 q = 1) : d8910 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1608, d8910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1608, d8910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1609 q = 1) (hb : d92313 q = 1) : d8911 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1609, d8911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1609, d8911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11308 (p : Pattern) (ha : d6403 p = 1) (hb : d92314 p = 1) : d8976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d92313 q = 1) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11307 q ha hb
    | true =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d92314 q = 1) : d8975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6403 q = 1) (hb : d92314 q = 1) : d8976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6403, d8976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6403, d8976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11309 (p : Pattern) (ha : d6409 p = 1) (hb : d92314 p = 1) : d93717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92314 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6404 q = 1) (hb : d92314 q = 1) : d93712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11308 q ha hb
    | true =>
      simp only [d6404, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6405 q = 1) (hb : d92314 q = 1) : d93713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6406 q = 1) (hb : d92314 q = 1) : d93714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6406, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6407 q = 1) (hb : d92314 q = 1) : d93715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6408 q = 1) (hb : d92314 q = 1) : d93716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6409 q = 1) (hb : d92314 q = 1) : d93717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11310 (p : Pattern) (ha : d6412 p = 1) (hb : d92314 p = 1) : d8998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d92313 q = 1) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11307 q ha hb
    | true =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6400 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d92314 q = 1) : d8975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d8975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6412 q = 1) (hb : d92314 q = 1) : d8998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6412, d8998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6412, d8998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11311 (p : Pattern) (ha : d6418 p = 1) (hb : d92314 p = 1) : d93725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92314 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6404 q = 1) (hb : d92314 q = 1) : d93712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11308 q ha hb
    | true =>
      simp only [d6404, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6405 q = 1) (hb : d92314 q = 1) : d93713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6406 q = 1) (hb : d92314 q = 1) : d93714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6406, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6407 q = 1) (hb : d92314 q = 1) : d93715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6408 q = 1) (hb : d92314 q = 1) : d93716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d92314 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6413 q = 1) (hb : d92314 q = 1) : d93720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11310 q ha hb
    | true =>
      simp only [d6413, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6414 q = 1) (hb : d92314 q = 1) : d93721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6414, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6415 q = 1) (hb : d92314 q = 1) : d93722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6415, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6416 q = 1) (hb : d92314 q = 1) : d93723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6417 q = 1) (hb : d92314 q = 1) : d93724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6418 q = 1) (hb : d92314 q = 1) : d93725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6418, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro11312 (p : Pattern) (ha : d5145 p = 1) (hb : d92313 p = 1) : d7036 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1592 q = 1) : d1592 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1606 q = 1) (hb : d92313 q = 1) : d7034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5143 q = 1) (hb : d92313 q = 1) : d5143 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5144 q = 1) (hb : d92313 q = 1) : d7035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5144, d7035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5144, d7035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5145 q = 1) (hb : d92313 q = 1) : d7036 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5145, d7036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5145, d7036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11313 (p : Pattern) (ha : d5151 p = 1) (hb : d92314 p = 1) : d93748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5146 q = 1) (hb : d92313 q = 1) : d7037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11312 q ha hb
    | true =>
      simp only [d5146, d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5147 q = 1) (hb : d92313 q = 1) : d7038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5147, d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5148 q = 1) (hb : d92314 q = 1) : d93745 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5148, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5149 q = 1) (hb : d92314 q = 1) : d93746 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5149, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5150 q = 1) (hb : d92314 q = 1) : d93747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5150, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5151 q = 1) (hb : d92314 q = 1) : d93748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5151, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5151, d93748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11314 (p : Pattern) (ha : d6478 p = 1) (hb : d92314 p = 1) : d93778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92314 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6473 q = 1) (hb : d92314 q = 1) : d93773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6473, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11313 q ha hb
    | true =>
      simp only [d6473, d93773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6474 q = 1) (hb : d92314 q = 1) : d93774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6474, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6474, d93774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6475 q = 1) (hb : d92314 q = 1) : d93775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6475, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6475, d93775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6476 q = 1) (hb : d92314 q = 1) : d93776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6476, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6476, d93776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6477 q = 1) (hb : d92314 q = 1) : d93777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6477, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6477, d93777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d92314 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6478 q = 1) (hb : d92314 q = 1) : d93778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6478, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6478, d93778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11315 (p : Pattern) (ha : d6423 p = 1) (hb : d92314 p = 1) : d93730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d92313 q = 1) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11307 q ha hb
    | true =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6422 q = 1) (hb : d92314 q = 1) : d93729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6422, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6423 q = 1) (hb : d92314 q = 1) : d93730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6423, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6423, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11316 (p : Pattern) (ha : d6430 p = 1) (hb : d92314 p = 1) : d93737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d92313 q = 1) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11307 q ha hb
    | true =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6428 q = 1) (hb : d92314 q = 1) : d93735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6428, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6429 q = 1) (hb : d92314 q = 1) : d93736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6429, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6430 q = 1) (hb : d92314 q = 1) : d93737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6430, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6430, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11317 (p : Pattern) (ha : d1676 p = 1) (hb : d92313 p = 1) : d8950 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1673 q = 1) : d1673 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1592 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1674 q = 1) (hb : d92313 q = 1) : d8948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d92313, d8948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1674, d92313, d8948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1592 q = 1) : d1592 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1605 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1606 q = 1) (hb : d92313 q = 1) : d7034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1675 q = 1) (hb : d92313 q = 1) : d8949 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1675, d8949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1675, d8949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1676 q = 1) (hb : d92313 q = 1) : d8950 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1676, d8950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1676, d8950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11318 (p : Pattern) (ha : d6437 p = 1) (hb : d92314 p = 1) : d93744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1677 q = 1) (hb : d92313 q = 1) : d8951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d8951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11317 q ha hb
    | true =>
      simp only [d1677, d8951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1678 q = 1) (hb : d92313 q = 1) : d8952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d8952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1678, d8952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6434 q = 1) (hb : d92314 q = 1) : d93741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6434, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6435 q = 1) (hb : d92314 q = 1) : d93742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6435, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6436 q = 1) (hb : d92314 q = 1) : d93743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6436, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6437 q = 1) (hb : d92314 q = 1) : d93744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6437, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6437, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11319 (p : Pattern) (ha : d76987 p = 1) (hb : d92314 p = 1) : d93754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92314 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6424 q = 1) (hb : d92314 q = 1) : d93731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11315 q ha hb
    | true =>
      simp only [d6424, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6425 q = 1) (hb : d92314 q = 1) : d93732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6426 q = 1) (hb : d92314 q = 1) : d93733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6426, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6427 q = 1) (hb : d92314 q = 1) : d93734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92314 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6431 q = 1) (hb : d92314 q = 1) : d93738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11316 q ha hb
    | true =>
      simp only [d6431, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6432 q = 1) (hb : d92314 q = 1) : d93739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6433 q = 1) (hb : d92314 q = 1) : d93740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6433, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6438 q = 1) (hb : d92314 q = 1) : d93749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11318 q ha hb
    | true =>
      simp only [d6438, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11313 q ha hb
  have h11 (q : Pattern) (ha : d76983 q = 1) (hb : d92314 q = 1) : d93750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76983, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6445 q = 1) (hb : d92314 q = 1) : d8977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11308 q ha hb
    | true =>
      simp only [d6445, d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6446 q = 1) (hb : d92314 q = 1) : d8978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6446, d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76984 q = 1) (hb : d92314 q = 1) : d93751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76984, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76985 q = 1) (hb : d92314 q = 1) : d93752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76985, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76986 q = 1) (hb : d92314 q = 1) : d93753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76986, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76987 q = 1) (hb : d92314 q = 1) : d93754 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76987, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76987, d93754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11320 (p : Pattern) (ha : d6451 p = 1) (hb : d92314 p = 1) : d93755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d92313 q = 1) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11307 q ha hb
    | true =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d92314 q = 1) : d8974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d8974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6422 q = 1) (hb : d92314 q = 1) : d93729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6422, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6451 q = 1) (hb : d92314 q = 1) : d93755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6451, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6451, d93755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11321 (p : Pattern) (ha : d6456 p = 1) (hb : d92314 p = 1) : d93760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d92313 q = 1) : d8912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11307 q ha hb
    | true =>
      simp only [d1610, d8912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d92313 q = 1) : d8913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d8913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d92314 q = 1) : d8973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d92314, d8973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6428 q = 1) (hb : d92314 q = 1) : d93735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6428, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6429 q = 1) (hb : d92314 q = 1) : d93736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6429, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6456 q = 1) (hb : d92314 q = 1) : d93760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6456, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6456, d93760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11322 (p : Pattern) (ha : d6460 p = 1) (hb : d92314 p = 1) : d93764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d92313 q = 1) : d8951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d8951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11317 q ha hb
    | true =>
      simp only [d1677, d8951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d92313 q = 1) : d8952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d8952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d8952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6434 q = 1) (hb : d92314 q = 1) : d93741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6434, d92314, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6435 q = 1) (hb : d92314 q = 1) : d93742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6435, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6436 q = 1) (hb : d92314 q = 1) : d93743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6436, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6460 q = 1) (hb : d92314 q = 1) : d93764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6460, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6460, d93764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11323 (p : Pattern) (ha : d6461 p = 1) (hb : d92314 p = 1) : d93765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d92313 q = 1) : d7037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11312 q ha hb
    | true =>
      simp only [d5146, d7037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d92313 q = 1) : d7038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d7038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5148 q = 1) (hb : d92314 q = 1) : d93745 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5148, d92314, d93745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5149 q = 1) (hb : d92314 q = 1) : d93746 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5149, d93746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5150 q = 1) (hb : d92314 q = 1) : d93747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5150, d93747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6461 q = 1) (hb : d92314 q = 1) : d93765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6461, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6461, d93765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11324 (p : Pattern) (ha : d76992 p = 1) (hb : d92314 p = 1) : d93771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92314 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6424 q = 1) (hb : d92314 q = 1) : d93731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11315 q ha hb
    | true =>
      simp only [d6424, d93731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6425 q = 1) (hb : d92314 q = 1) : d93732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d93732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6426 q = 1) (hb : d92314 q = 1) : d93733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6426, d93733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6427 q = 1) (hb : d92314 q = 1) : d93734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d93734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92314 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6431 q = 1) (hb : d92314 q = 1) : d93738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11316 q ha hb
    | true =>
      simp only [d6431, d93738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6432 q = 1) (hb : d92314 q = 1) : d93739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d93739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6433 q = 1) (hb : d92314 q = 1) : d93740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6433, d93740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6438 q = 1) (hb : d92314 q = 1) : d93749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11318 q ha hb
    | true =>
      simp only [d6438, d93749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11313 q ha hb
  have h11 (q : Pattern) (ha : d76983 q = 1) (hb : d92314 q = 1) : d93750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76983, d93750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6445 q = 1) (hb : d92314 q = 1) : d8977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11308 q ha hb
    | true =>
      simp only [d6445, d8977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6446 q = 1) (hb : d92314 q = 1) : d8978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6446, d8978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76984 q = 1) (hb : d92314 q = 1) : d93751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76984, d93751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76985 q = 1) (hb : d92314 q = 1) : d93752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76985, d93752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76986 q = 1) (hb : d92314 q = 1) : d93753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76986, d93753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1804 q = 1) (hb : d92314 q = 1) : d1804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6452 q = 1) (hb : d92314 q = 1) : d93756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6452, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11320 q ha hb
    | true =>
      simp only [d6452, d93756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6453 q = 1) (hb : d92314 q = 1) : d93757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6453, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6453, d93757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6454 q = 1) (hb : d92314 q = 1) : d93758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6454, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6454, d93758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6455 q = 1) (hb : d92314 q = 1) : d93759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6455, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6455, d93759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1810 q = 1) (hb : d92314 q = 1) : d1810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6457 q = 1) (hb : d92314 q = 1) : d93761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6457, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11321 q ha hb
    | true =>
      simp only [d6457, d93761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6458 q = 1) (hb : d92314 q = 1) : d93762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6458, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6458, d93762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6459 q = 1) (hb : d92314 q = 1) : d93763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6459, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6459, d93763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6462 q = 1) (hb : d92314 q = 1) : d93766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11322 q ha hb
    | true =>
      simp only [d6462, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11323 q ha hb
  have h27 (q : Pattern) (ha : d76988 q = 1) (hb : d92314 q = 1) : d93767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76988, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6466 q = 1) (hb : d92314 q = 1) : d8999 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11310 q ha hb
    | true =>
      simp only [d6466, d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6467 q = 1) (hb : d92314 q = 1) : d9000 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6467, d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76989 q = 1) (hb : d92314 q = 1) : d93768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76989, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76990 q = 1) (hb : d92314 q = 1) : d93769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76990, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76990, d93769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76991 q = 1) (hb : d92314 q = 1) : d93770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76991, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76991, d93770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76992 q = 1) (hb : d92314 q = 1) : d93771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76992, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76992, d93771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11325 (p : Pattern) (ha : d76999 p = 1) (hb : d92314 p = 1) : d93785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6462 q = 1) (hb : d92314 q = 1) : d93766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11322 q ha hb
    | true =>
      simp only [d6462, d93766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11323 q ha hb
  have h2 (q : Pattern) (ha : d76988 q = 1) (hb : d92314 q = 1) : d93767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76988, d93767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6466 q = 1) (hb : d92314 q = 1) : d8999 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11310 q ha hb
    | true =>
      simp only [d6466, d8999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6467 q = 1) (hb : d92314 q = 1) : d9000 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6467, d9000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76989 q = 1) (hb : d92314 q = 1) : d93768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76989, d93768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76997 q = 1) (hb : d92314 q = 1) : d93783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76997, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76997, d93783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76998 q = 1) (hb : d92314 q = 1) : d93784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76998, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76998, d93784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76999 q = 1) (hb : d92314 q = 1) : d93785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76999, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76999, d93785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11326 (p : Pattern) (ha : d1894 p = 1) (hb : d92313 p = 1) : d9026 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1876 q = 1) : d1876 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1882 q = 1) (hb : d92313 q = 1) : d9024 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d92313, d9024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1882, d92313, d9024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1881 q = 1) : d1881 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1891 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1892 q = 1) (hb : d92313 q = 1) : d7080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1893 q = 1) (hb : d92313 q = 1) : d9025 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d9025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1893, d9025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1894 q = 1) (hb : d92313 q = 1) : d9026 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d9026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1894, d9026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11327 (p : Pattern) (ha : d6494 p = 1) (hb : d92314 p = 1) : d93794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d92313 q = 1) : d9027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d9027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11326 q ha hb
    | true =>
      simp only [d1895, d9027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d92313 q = 1) : d9028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d9028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d9028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6491 q = 1) (hb : d92314 q = 1) : d93791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6491, d92314, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6491, d92314, d93791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6492 q = 1) (hb : d92314 q = 1) : d93792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6492, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6492, d93792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6493 q = 1) (hb : d92314 q = 1) : d93793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6493, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6493, d93793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6494 q = 1) (hb : d92314 q = 1) : d93794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6494, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6494, d93794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11328 (p : Pattern) (ha : d6507 p = 1) (hb : d92313 p = 1) : d7082 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1881 q = 1) : d1881 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1891 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1892 q = 1) (hb : d92313 q = 1) : d7080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6505 q = 1) (hb : d92313 q = 1) : d6505 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6506 q = 1) (hb : d92313 q = 1) : d7081 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6506, d7081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6506, d7081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6507 q = 1) (hb : d92313 q = 1) : d7082 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6507, d7082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6507, d7082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11329 (p : Pattern) (ha : d6513 p = 1) (hb : d92314 p = 1) : d93798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6508 q = 1) (hb : d92313 q = 1) : d7083 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d7083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11328 q ha hb
    | true =>
      simp only [d6508, d7083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6509 q = 1) (hb : d92313 q = 1) : d7084 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, d7084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6509, d7084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6510 q = 1) (hb : d92314 q = 1) : d93795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6510, d92314, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6510, d92314, d93795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6511 q = 1) (hb : d92314 q = 1) : d93796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6511, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6511, d93796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6512 q = 1) (hb : d92314 q = 1) : d93797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6512, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6512, d93797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6513 q = 1) (hb : d92314 q = 1) : d93798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6513, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6513, d93798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11330 (p : Pattern) (ha : d1899 p = 1) (hb : d92313 p = 1) : d9050 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1881 q = 1) : d1881 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1891 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1892 q = 1) (hb : d92313 q = 1) : d7080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1897 q = 1) (hb : d92313 q = 1) : d1897 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1898 q = 1) (hb : d92313 q = 1) : d9049 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d9049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1898, d9049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1899 q = 1) (hb : d92313 q = 1) : d9050 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d9050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1899, d9050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11331 (p : Pattern) (ha : d6524 p = 1) (hb : d92314 p = 1) : d9056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d92313 q = 1) : d9051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d9051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11330 q ha hb
    | true =>
      simp only [d1900, d9051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d92313 q = 1) : d9052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d9052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d9052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6521 q = 1) (hb : d92314 q = 1) : d9053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, d92314, d9053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6521, d92314, d9053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6522 q = 1) (hb : d92314 q = 1) : d9054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, d9054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6522, d9054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6523 q = 1) (hb : d92314 q = 1) : d9055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, d9055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6523, d9055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6524 q = 1) (hb : d92314 q = 1) : d9056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, d9056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6524, d9056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11332 (p : Pattern) (ha : d77009 p = 1) (hb : d92314 p = 1) : d93804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6514 q = 1) (hb : d92314 q = 1) : d93799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6514, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11327 q ha hb
    | true =>
      simp only [d6514, d93799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11329 q ha hb
  have h2 (q : Pattern) (ha : d77005 q = 1) (hb : d92314 q = 1) : d93800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77005, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77005, d93800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6525 q = 1) (hb : d92314 q = 1) : d9057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d9057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11331 q ha hb
    | true =>
      simp only [d6525, d9057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6526 q = 1) (hb : d92314 q = 1) : d9058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d9058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6526, d9058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77006 q = 1) (hb : d92314 q = 1) : d93801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77006, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77006, d93801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77007 q = 1) (hb : d92314 q = 1) : d93802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77007, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77007, d93802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77008 q = 1) (hb : d92314 q = 1) : d93803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77008, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77008, d93803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77009 q = 1) (hb : d92314 q = 1) : d93804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77009, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77009, d93804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11333 (p : Pattern) (ha : d77015 p = 1) (hb : d92314 p = 1) : d93810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6410 q = 1) (hb : d92314 q = 1) : d93718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6410, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6410, d93718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11309 q ha hb
  have h2 (q : Pattern) (ha : d6411 q = 1) (hb : d92314 q = 1) : d93719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6411, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6411, d93719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6419 q = 1) (hb : d92314 q = 1) : d93726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11309 q ha hb
    | true =>
      simp only [d6419, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11311 q ha hb
  have h4 (q : Pattern) (ha : d6420 q = 1) (hb : d92314 q = 1) : d93727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6420, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6421 q = 1) (hb : d92314 q = 1) : d93728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6421, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6421, d93728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76993 q = 1) (hb : d92314 q = 1) : d93772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76993, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11319 q ha hb
    | true =>
      simp only [d76993, d93772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11324 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d92314 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6479 q = 1) (hb : d92314 q = 1) : d93779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6479, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11314 q ha hb
    | true =>
      simp only [d6479, d93779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76994 q = 1) (hb : d92314 q = 1) : d93780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76994, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76994, d93780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76995 q = 1) (hb : d92314 q = 1) : d93781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76995, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76995, d93781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76996 q = 1) (hb : d92314 q = 1) : d93782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76996, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76996, d93782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d77000 q = 1) (hb : d92314 q = 1) : d93786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77000, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77000, d93786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11325 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d92314 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d77001 q = 1) (hb : d92314 q = 1) : d93787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77001, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77001, d93787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77002 q = 1) (hb : d92314 q = 1) : d93788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77002, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77002, d93788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77003 q = 1) (hb : d92314 q = 1) : d93789 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77003, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77003, d93789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d77004 q = 1) (hb : d92314 q = 1) : d93790 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77004, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77004, d93790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77010 q = 1) (hb : d92314 q = 1) : d93805 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77010, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77010, d93805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11332 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d92314 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d77011 q = 1) (hb : d92314 q = 1) : d93806 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77011, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d77011, d93806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d77012 q = 1) (hb : d92314 q = 1) : d93807 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77012, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77012, d93807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77013 q = 1) (hb : d92314 q = 1) : d93808 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77013, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77013, d93808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77014 q = 1) (hb : d92314 q = 1) : d93809 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77014, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d77014, d93809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d77015 q = 1) (hb : d92314 q = 1) : d93810 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77015, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77015, d93810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro11334 (p : Pattern) (ha : d77021 p = 1) (hb : d92314 p = 1) : d93816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77016 q = 1) (hb : d92314 q = 1) : d93811 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77016, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77016, d93811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11333 q ha hb
  have h2 (q : Pattern) (ha : d77017 q = 1) (hb : d92314 q = 1) : d93812 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77017, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77017, d93812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77018 q = 1) (hb : d92314 q = 1) : d93813 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77018, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77018, d93813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77019 q = 1) (hb : d92314 q = 1) : d93814 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77019, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77019, d93814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77020 q = 1) (hb : d92314 q = 1) : d93815 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77020, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77020, d93815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77021 q = 1) (hb : d92314 q = 1) : d93816 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77021, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77021, d93816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11335 (p : Pattern) (ha : d2092 p = 1) (hb : d92313 p = 1) : d9080 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2075 q = 1) : d2075 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2088 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2089 q = 1) (hb : d92313 q = 1) : d7115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2090 q = 1) (hb : d92313 q = 1) : d2090 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2091 q = 1) (hb : d92313 q = 1) : d9079 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2091, d9079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2091, d9079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2092 q = 1) (hb : d92313 q = 1) : d9080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2092, d9080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2092, d9080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11336 (p : Pattern) (ha : d6550 p = 1) (hb : d92314 p = 1) : d9145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d92313 q = 1) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11335 q ha hb
    | true =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d92314 q = 1) : d9144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6550 q = 1) (hb : d92314 q = 1) : d9145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, d9145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6550, d9145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11337 (p : Pattern) (ha : d6556 p = 1) (hb : d92314 p = 1) : d93826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92314 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6551 q = 1) (hb : d92314 q = 1) : d93821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11336 q ha hb
    | true =>
      simp only [d6551, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6552 q = 1) (hb : d92314 q = 1) : d93822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6553 q = 1) (hb : d92314 q = 1) : d93823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6553, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6554 q = 1) (hb : d92314 q = 1) : d93824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6555 q = 1) (hb : d92314 q = 1) : d93825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6556 q = 1) (hb : d92314 q = 1) : d93826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11338 (p : Pattern) (ha : d6559 p = 1) (hb : d92314 p = 1) : d9167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d92313 q = 1) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11335 q ha hb
    | true =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d92314 q = 1) : d9144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d9144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6559 q = 1) (hb : d92314 q = 1) : d9167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, d9167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6559, d9167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11339 (p : Pattern) (ha : d6565 p = 1) (hb : d92314 p = 1) : d93834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92314 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6551 q = 1) (hb : d92314 q = 1) : d93821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11336 q ha hb
    | true =>
      simp only [d6551, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6552 q = 1) (hb : d92314 q = 1) : d93822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6553 q = 1) (hb : d92314 q = 1) : d93823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6553, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6554 q = 1) (hb : d92314 q = 1) : d93824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6555 q = 1) (hb : d92314 q = 1) : d93825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d92314 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6560 q = 1) (hb : d92314 q = 1) : d93829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11338 q ha hb
    | true =>
      simp only [d6560, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6561 q = 1) (hb : d92314 q = 1) : d93830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6561, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6562 q = 1) (hb : d92314 q = 1) : d93831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6562, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6563 q = 1) (hb : d92314 q = 1) : d93832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6564 q = 1) (hb : d92314 q = 1) : d93833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6565 q = 1) (hb : d92314 q = 1) : d93834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6565, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro11340 (p : Pattern) (ha : d5258 p = 1) (hb : d92313 p = 1) : d7117 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2075 q = 1) : d2075 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2088 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2089 q = 1) (hb : d92313 q = 1) : d7115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5256 q = 1) (hb : d92313 q = 1) : d5256 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5257 q = 1) (hb : d92313 q = 1) : d7116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5257, d7116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5257, d7116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5258 q = 1) (hb : d92313 q = 1) : d7117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5258, d7117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5258, d7117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11341 (p : Pattern) (ha : d5264 p = 1) (hb : d92314 p = 1) : d93857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5259 q = 1) (hb : d92313 q = 1) : d7118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11340 q ha hb
    | true =>
      simp only [d5259, d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5260 q = 1) (hb : d92313 q = 1) : d7119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5260, d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5261 q = 1) (hb : d92314 q = 1) : d93854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5261, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5262 q = 1) (hb : d92314 q = 1) : d93855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5262, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5263 q = 1) (hb : d92314 q = 1) : d93856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5263, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5264 q = 1) (hb : d92314 q = 1) : d93857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5264, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5264, d93857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11342 (p : Pattern) (ha : d6625 p = 1) (hb : d92314 p = 1) : d93887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92314 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6620 q = 1) (hb : d92314 q = 1) : d93882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6620, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11341 q ha hb
    | true =>
      simp only [d6620, d93882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6621 q = 1) (hb : d92314 q = 1) : d93883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6621, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6621, d93883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6622 q = 1) (hb : d92314 q = 1) : d93884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6622, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6622, d93884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6623 q = 1) (hb : d92314 q = 1) : d93885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6623, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6623, d93885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6624 q = 1) (hb : d92314 q = 1) : d93886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6624, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6624, d93886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d92314 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6625 q = 1) (hb : d92314 q = 1) : d93887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6625, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6625, d93887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11343 (p : Pattern) (ha : d6570 p = 1) (hb : d92314 p = 1) : d93839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d92313 q = 1) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11335 q ha hb
    | true =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6569 q = 1) (hb : d92314 q = 1) : d93838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6570 q = 1) (hb : d92314 q = 1) : d93839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6570, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6570, d93839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11344 (p : Pattern) (ha : d6577 p = 1) (hb : d92314 p = 1) : d93846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d92313 q = 1) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11335 q ha hb
    | true =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6575 q = 1) (hb : d92314 q = 1) : d93844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6576 q = 1) (hb : d92314 q = 1) : d93845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6576, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6577 q = 1) (hb : d92314 q = 1) : d93846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6577, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6577, d93846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11345 (p : Pattern) (ha : d2155 p = 1) (hb : d92313 p = 1) : d9119 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2152 q = 1) : d2152 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2075 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2153 q = 1) (hb : d92313 q = 1) : d9117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d92313, d9117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2153, d92313, d9117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d2075 q = 1) : d2075 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2088 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2089 q = 1) (hb : d92313 q = 1) : d7115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2154 q = 1) (hb : d92313 q = 1) : d9118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2154, d9118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2154, d9118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2155 q = 1) (hb : d92313 q = 1) : d9119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2155, d9119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2155, d9119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11346 (p : Pattern) (ha : d6584 p = 1) (hb : d92314 p = 1) : d93853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2156 q = 1) (hb : d92313 q = 1) : d9120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d9120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11345 q ha hb
    | true =>
      simp only [d2156, d9120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2157 q = 1) (hb : d92313 q = 1) : d9121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d9121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2157, d9121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6581 q = 1) (hb : d92314 q = 1) : d93850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6581, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6582 q = 1) (hb : d92314 q = 1) : d93851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6582, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6583 q = 1) (hb : d92314 q = 1) : d93852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6583, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6584 q = 1) (hb : d92314 q = 1) : d93853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6584, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6584, d93853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11347 (p : Pattern) (ha : d77030 p = 1) (hb : d92314 p = 1) : d93863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92314 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6571 q = 1) (hb : d92314 q = 1) : d93840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11343 q ha hb
    | true =>
      simp only [d6571, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6572 q = 1) (hb : d92314 q = 1) : d93841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6573 q = 1) (hb : d92314 q = 1) : d93842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6573, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6574 q = 1) (hb : d92314 q = 1) : d93843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92314 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6578 q = 1) (hb : d92314 q = 1) : d93847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11344 q ha hb
    | true =>
      simp only [d6578, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6579 q = 1) (hb : d92314 q = 1) : d93848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6580 q = 1) (hb : d92314 q = 1) : d93849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6580, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6585 q = 1) (hb : d92314 q = 1) : d93858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11346 q ha hb
    | true =>
      simp only [d6585, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11341 q ha hb
  have h11 (q : Pattern) (ha : d77026 q = 1) (hb : d92314 q = 1) : d93859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77026, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6592 q = 1) (hb : d92314 q = 1) : d9146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11336 q ha hb
    | true =>
      simp only [d6592, d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6593 q = 1) (hb : d92314 q = 1) : d9147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6593, d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d77027 q = 1) (hb : d92314 q = 1) : d93860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77027, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77028 q = 1) (hb : d92314 q = 1) : d93861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77028, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77029 q = 1) (hb : d92314 q = 1) : d93862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77029, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77030 q = 1) (hb : d92314 q = 1) : d93863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77030, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77030, d93863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11348 (p : Pattern) (ha : d6598 p = 1) (hb : d92314 p = 1) : d93864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d92313 q = 1) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11335 q ha hb
    | true =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d92314 q = 1) : d9143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d9143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6569 q = 1) (hb : d92314 q = 1) : d93838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d93838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6598 q = 1) (hb : d92314 q = 1) : d93864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6598, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6598, d93864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11349 (p : Pattern) (ha : d6603 p = 1) (hb : d92314 p = 1) : d93869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d92313 q = 1) : d9081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11335 q ha hb
    | true =>
      simp only [d2093, d9081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d92313 q = 1) : d9082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d9082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d92314 q = 1) : d9142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d92314, d9142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6575 q = 1) (hb : d92314 q = 1) : d93844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d93844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6576 q = 1) (hb : d92314 q = 1) : d93845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6576, d93845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6603 q = 1) (hb : d92314 q = 1) : d93869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6603, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6603, d93869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11350 (p : Pattern) (ha : d6607 p = 1) (hb : d92314 p = 1) : d93873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d92313 q = 1) : d9120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d9120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11345 q ha hb
    | true =>
      simp only [d2156, d9120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d92313 q = 1) : d9121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d9121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d9121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6581 q = 1) (hb : d92314 q = 1) : d93850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6581, d92314, d93850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6582 q = 1) (hb : d92314 q = 1) : d93851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6582, d93851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6583 q = 1) (hb : d92314 q = 1) : d93852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6583, d93852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6607 q = 1) (hb : d92314 q = 1) : d93873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6607, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6607, d93873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11351 (p : Pattern) (ha : d6608 p = 1) (hb : d92314 p = 1) : d93874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d92313 q = 1) : d7118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11340 q ha hb
    | true =>
      simp only [d5259, d7118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d92313 q = 1) : d7119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d7119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5261 q = 1) (hb : d92314 q = 1) : d93854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5261, d92314, d93854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5262 q = 1) (hb : d92314 q = 1) : d93855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5262, d93855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5263 q = 1) (hb : d92314 q = 1) : d93856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5263, d93856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6608 q = 1) (hb : d92314 q = 1) : d93874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6608, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6608, d93874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11352 (p : Pattern) (ha : d77035 p = 1) (hb : d92314 p = 1) : d93880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92314 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6571 q = 1) (hb : d92314 q = 1) : d93840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11343 q ha hb
    | true =>
      simp only [d6571, d93840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6572 q = 1) (hb : d92314 q = 1) : d93841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d93841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6573 q = 1) (hb : d92314 q = 1) : d93842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6573, d93842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6574 q = 1) (hb : d92314 q = 1) : d93843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d93843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92314 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6578 q = 1) (hb : d92314 q = 1) : d93847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11344 q ha hb
    | true =>
      simp only [d6578, d93847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6579 q = 1) (hb : d92314 q = 1) : d93848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d93848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6580 q = 1) (hb : d92314 q = 1) : d93849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6580, d93849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6585 q = 1) (hb : d92314 q = 1) : d93858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11346 q ha hb
    | true =>
      simp only [d6585, d93858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11341 q ha hb
  have h11 (q : Pattern) (ha : d77026 q = 1) (hb : d92314 q = 1) : d93859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77026, d93859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6592 q = 1) (hb : d92314 q = 1) : d9146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11336 q ha hb
    | true =>
      simp only [d6592, d9146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6593 q = 1) (hb : d92314 q = 1) : d9147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6593, d9147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d77027 q = 1) (hb : d92314 q = 1) : d93860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77027, d93860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77028 q = 1) (hb : d92314 q = 1) : d93861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77028, d93861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77029 q = 1) (hb : d92314 q = 1) : d93862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77029, d93862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2282 q = 1) (hb : d92314 q = 1) : d2282 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6599 q = 1) (hb : d92314 q = 1) : d93865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6599, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11348 q ha hb
    | true =>
      simp only [d6599, d93865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6600 q = 1) (hb : d92314 q = 1) : d93866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6600, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6600, d93866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6601 q = 1) (hb : d92314 q = 1) : d93867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6601, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6601, d93867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6602 q = 1) (hb : d92314 q = 1) : d93868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6602, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6602, d93868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d2288 q = 1) (hb : d92314 q = 1) : d2288 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6604 q = 1) (hb : d92314 q = 1) : d93870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6604, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11349 q ha hb
    | true =>
      simp only [d6604, d93870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6605 q = 1) (hb : d92314 q = 1) : d93871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6605, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6605, d93871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6606 q = 1) (hb : d92314 q = 1) : d93872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6606, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6606, d93872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6609 q = 1) (hb : d92314 q = 1) : d93875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11350 q ha hb
    | true =>
      simp only [d6609, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11351 q ha hb
  have h27 (q : Pattern) (ha : d77031 q = 1) (hb : d92314 q = 1) : d93876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d77031, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6613 q = 1) (hb : d92314 q = 1) : d9168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11338 q ha hb
    | true =>
      simp only [d6613, d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6614 q = 1) (hb : d92314 q = 1) : d9169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6614, d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d77032 q = 1) (hb : d92314 q = 1) : d93877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d77032, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d77033 q = 1) (hb : d92314 q = 1) : d93878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77033, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d77033, d93878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d77034 q = 1) (hb : d92314 q = 1) : d93879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77034, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77034, d93879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d77035 q = 1) (hb : d92314 q = 1) : d93880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77035, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77035, d93880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11353 (p : Pattern) (ha : d77042 p = 1) (hb : d92314 p = 1) : d93894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6609 q = 1) (hb : d92314 q = 1) : d93875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11350 q ha hb
    | true =>
      simp only [d6609, d93875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11351 q ha hb
  have h2 (q : Pattern) (ha : d77031 q = 1) (hb : d92314 q = 1) : d93876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77031, d93876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6613 q = 1) (hb : d92314 q = 1) : d9168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11338 q ha hb
    | true =>
      simp only [d6613, d9168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6614 q = 1) (hb : d92314 q = 1) : d9169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6614, d9169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77032 q = 1) (hb : d92314 q = 1) : d93877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77032, d93877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77040 q = 1) (hb : d92314 q = 1) : d93892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77040, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77040, d93892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77041 q = 1) (hb : d92314 q = 1) : d93893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77041, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77041, d93893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77042 q = 1) (hb : d92314 q = 1) : d93894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77042, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77042, d93894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11354 (p : Pattern) (ha : d2372 p = 1) (hb : d92313 p = 1) : d9195 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2354 q = 1) : d2354 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2360 q = 1) (hb : d92313 q = 1) : d9193 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d92313, d9193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2360, d92313, d9193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d2359 q = 1) : d2359 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2369 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2370 q = 1) (hb : d92313 q = 1) : d7161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2371 q = 1) (hb : d92313 q = 1) : d9194 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2371, d9194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2371, d9194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2372 q = 1) (hb : d92313 q = 1) : d9195 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2372, d9195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2372, d9195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11355 (p : Pattern) (ha : d6641 p = 1) (hb : d92314 p = 1) : d93903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d92313 q = 1) : d9196 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d9196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11354 q ha hb
    | true =>
      simp only [d2373, d9196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d92313 q = 1) : d9197 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d9197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d9197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6638 q = 1) (hb : d92314 q = 1) : d93900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6638, d92314, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6638, d92314, d93900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6639 q = 1) (hb : d92314 q = 1) : d93901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6639, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6639, d93901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6640 q = 1) (hb : d92314 q = 1) : d93902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6640, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6640, d93902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6641 q = 1) (hb : d92314 q = 1) : d93903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6641, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6641, d93903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11356 (p : Pattern) (ha : d6654 p = 1) (hb : d92313 p = 1) : d7163 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2359 q = 1) : d2359 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2369 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2370 q = 1) (hb : d92313 q = 1) : d7161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6652 q = 1) (hb : d92313 q = 1) : d6652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6653 q = 1) (hb : d92313 q = 1) : d7162 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6653, d7162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6653, d7162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6654 q = 1) (hb : d92313 q = 1) : d7163 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6654, d7163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6654, d7163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11357 (p : Pattern) (ha : d6660 p = 1) (hb : d92314 p = 1) : d93907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6655 q = 1) (hb : d92313 q = 1) : d7164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, d7164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11356 q ha hb
    | true =>
      simp only [d6655, d7164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d92313 q = 1) : d7165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d7165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d7165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6657 q = 1) (hb : d92314 q = 1) : d93904 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6657, d92314, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6657, d92314, d93904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6658 q = 1) (hb : d92314 q = 1) : d93905 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6658, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6658, d93905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6659 q = 1) (hb : d92314 q = 1) : d93906 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6659, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6659, d93906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6660 q = 1) (hb : d92314 q = 1) : d93907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6660, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6660, d93907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11358 (p : Pattern) (ha : d2377 p = 1) (hb : d92313 p = 1) : d9219 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2359 q = 1) : d2359 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2369 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2370 q = 1) (hb : d92313 q = 1) : d7161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2375 q = 1) (hb : d92313 q = 1) : d2375 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2376 q = 1) (hb : d92313 q = 1) : d9218 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2376, d9218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2376, d9218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2377 q = 1) (hb : d92313 q = 1) : d9219 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2377, d9219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2377, d9219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11359 (p : Pattern) (ha : d6671 p = 1) (hb : d92314 p = 1) : d9225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d92313 q = 1) : d9220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d9220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11358 q ha hb
    | true =>
      simp only [d2378, d9220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d92313 q = 1) : d9221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d9221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d9221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6668 q = 1) (hb : d92314 q = 1) : d9222 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, d92314, d9222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6668, d92314, d9222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6669 q = 1) (hb : d92314 q = 1) : d9223 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, d9223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6669, d9223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6670 q = 1) (hb : d92314 q = 1) : d9224 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, d9224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6670, d9224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6671 q = 1) (hb : d92314 q = 1) : d9225 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, d9225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6671, d9225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11360 (p : Pattern) (ha : d77052 p = 1) (hb : d92314 p = 1) : d93913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6661 q = 1) (hb : d92314 q = 1) : d93908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6661, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11355 q ha hb
    | true =>
      simp only [d6661, d93908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11357 q ha hb
  have h2 (q : Pattern) (ha : d77048 q = 1) (hb : d92314 q = 1) : d93909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77048, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77048, d93909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d92314 q = 1) : d9226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d9226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11359 q ha hb
    | true =>
      simp only [d6672, d9226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6673 q = 1) (hb : d92314 q = 1) : d9227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d9227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6673, d9227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77049 q = 1) (hb : d92314 q = 1) : d93910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77049, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77049, d93910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77050 q = 1) (hb : d92314 q = 1) : d93911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77050, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77050, d93911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77051 q = 1) (hb : d92314 q = 1) : d93912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77051, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77051, d93912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77052 q = 1) (hb : d92314 q = 1) : d93913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77052, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77052, d93913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11361 (p : Pattern) (ha : d77058 p = 1) (hb : d92314 p = 1) : d93919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6557 q = 1) (hb : d92314 q = 1) : d93827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6557, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6557, d93827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11337 q ha hb
  have h2 (q : Pattern) (ha : d6558 q = 1) (hb : d92314 q = 1) : d93828 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6558, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6558, d93828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6566 q = 1) (hb : d92314 q = 1) : d93835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11337 q ha hb
    | true =>
      simp only [d6566, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11339 q ha hb
  have h4 (q : Pattern) (ha : d6567 q = 1) (hb : d92314 q = 1) : d93836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6567, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6568 q = 1) (hb : d92314 q = 1) : d93837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6568, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6568, d93837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77036 q = 1) (hb : d92314 q = 1) : d93881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77036, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11347 q ha hb
    | true =>
      simp only [d77036, d93881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11352 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d92314 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6626 q = 1) (hb : d92314 q = 1) : d93888 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6626, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11342 q ha hb
    | true =>
      simp only [d6626, d93888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77037 q = 1) (hb : d92314 q = 1) : d93889 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77037, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77037, d93889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77038 q = 1) (hb : d92314 q = 1) : d93890 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77038, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77038, d93890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d77039 q = 1) (hb : d92314 q = 1) : d93891 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77039, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77039, d93891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d77043 q = 1) (hb : d92314 q = 1) : d93895 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77043, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77043, d93895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11353 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d92314 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d77044 q = 1) (hb : d92314 q = 1) : d93896 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77044, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77044, d93896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77045 q = 1) (hb : d92314 q = 1) : d93897 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77045, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77045, d93897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77046 q = 1) (hb : d92314 q = 1) : d93898 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77046, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77046, d93898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d77047 q = 1) (hb : d92314 q = 1) : d93899 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77047, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77047, d93899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77053 q = 1) (hb : d92314 q = 1) : d93914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77053, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77053, d93914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11360 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d92314 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d77054 q = 1) (hb : d92314 q = 1) : d93915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77054, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d77054, d93915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d77055 q = 1) (hb : d92314 q = 1) : d93916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77055, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77055, d93916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77056 q = 1) (hb : d92314 q = 1) : d93917 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77056, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77056, d93917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77057 q = 1) (hb : d92314 q = 1) : d93918 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77057, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d77057, d93918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d77058 q = 1) (hb : d92314 q = 1) : d93919 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77058, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77058, d93919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro11362 (p : Pattern) (ha : d77064 p = 1) (hb : d92314 p = 1) : d93925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77059 q = 1) (hb : d92314 q = 1) : d93920 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77059, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77059, d93920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11361 q ha hb
  have h2 (q : Pattern) (ha : d77060 q = 1) (hb : d92314 q = 1) : d93921 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77060, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77060, d93921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77061 q = 1) (hb : d92314 q = 1) : d93922 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77061, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77061, d93922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77062 q = 1) (hb : d92314 q = 1) : d93923 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77062, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77062, d93923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77063 q = 1) (hb : d92314 q = 1) : d93924 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77063, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77063, d93924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77064 q = 1) (hb : d92314 q = 1) : d93925 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77064, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77064, d93925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11363 (p : Pattern) (ha : d77070 p = 1) (hb : d92314 p = 1) : d93931 p = 1 := by
  have h0 (q : Pattern) (ha : d76899 q = 1) (hb : d92314 q = 1) : d93496 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76899, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11222 q ha hb
    | true =>
      simp only [d76899, d93496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11250 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76939 q = 1) (hb : d92314 q = 1) : d93602 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76939, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76939, d93602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11278 q ha hb
  have h3 (q : Pattern) (ha : d76940 q = 1) (hb : d92314 q = 1) : d93603 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76940, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76940, d93603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76980 q = 1) (hb : d92314 q = 1) : d93709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76980, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76980, d93709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11306 q ha hb
  have h5 (q : Pattern) (ha : d76981 q = 1) (hb : d92314 q = 1) : d93710 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76981, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76981, d93710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76982 q = 1) (hb : d92314 q = 1) : d93711 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76982, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76982, d93711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77022 q = 1) (hb : d92314 q = 1) : d93817 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77022, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77022, d93817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11334 q ha hb
  have h8 (q : Pattern) (ha : d77023 q = 1) (hb : d92314 q = 1) : d93818 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77023, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77023, d93818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77024 q = 1) (hb : d92314 q = 1) : d93819 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77024, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77024, d93819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77025 q = 1) (hb : d92314 q = 1) : d93820 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77025, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77025, d93820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77065 q = 1) (hb : d92314 q = 1) : d93926 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77065, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77065, d93926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11362 q ha hb
  have h12 (q : Pattern) (ha : d77066 q = 1) (hb : d92314 q = 1) : d93927 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77066, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77066, d93927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77067 q = 1) (hb : d92314 q = 1) : d93928 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77067, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77067, d93928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77068 q = 1) (hb : d92314 q = 1) : d93929 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77068, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77068, d93929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77069 q = 1) (hb : d92314 q = 1) : d93930 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77069, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77069, d93930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77070 q = 1) (hb : d92314 q = 1) : d93931 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77070, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77070, d93931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro11364 (p : Pattern) (ha : d77076 p = 1) (hb : d92314 p = 1) : d93937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77071 q = 1) (hb : d92314 q = 1) : d93932 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77071, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11363 q ha hb
    | true =>
      simp only [d77071, d93932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77072 q = 1) (hb : d92314 q = 1) : d93933 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77072, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77072, d93933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77073 q = 1) (hb : d92314 q = 1) : d93934 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77073, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77073, d93934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77074 q = 1) (hb : d92314 q = 1) : d93935 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77074, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77074, d93935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77075 q = 1) (hb : d92314 q = 1) : d93936 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77075, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77075, d93936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77076 q = 1) (hb : d92314 q = 1) : d93937 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77076, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77076, d93937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11365 (p : Pattern) (ha : d77082 p = 1) (hb : d92314 p = 1) : d93943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77077 q = 1) (hb : d92314 q = 1) : d93938 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77077, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11364 q ha hb
    | true =>
      simp only [d77077, d93938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77078 q = 1) (hb : d92314 q = 1) : d93939 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77078, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77078, d93939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77079 q = 1) (hb : d92314 q = 1) : d93940 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77079, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77079, d93940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77080 q = 1) (hb : d92314 q = 1) : d93941 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77080, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77080, d93941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77081 q = 1) (hb : d92314 q = 1) : d93942 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77081, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77081, d93942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77082 q = 1) (hb : d92314 q = 1) : d93943 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77082, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77082, d93943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11366 (p : Pattern) (ha : d77088 p = 1) (hb : d92314 p = 1) : d93949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77083 q = 1) (hb : d92314 q = 1) : d93944 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77083, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11365 q ha hb
    | true =>
      simp only [d77083, d93944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77084 q = 1) (hb : d92314 q = 1) : d93945 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77084, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77084, d93945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77085 q = 1) (hb : d92314 q = 1) : d93946 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77085, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77085, d93946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77086 q = 1) (hb : d92314 q = 1) : d93947 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77086, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77086, d93947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77087 q = 1) (hb : d92314 q = 1) : d93948 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77087, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77087, d93948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77088 q = 1) (hb : d92314 q = 1) : d93949 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77088, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77088, d93949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11367 (p : Pattern) (ha : d77094 p = 1) (hb : d92314 p = 1) : d93955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77089 q = 1) (hb : d92314 q = 1) : d93950 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11366 q ha hb
    | true =>
      simp only [d77089, d93950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77090 q = 1) (hb : d92314 q = 1) : d93951 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d93951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77091 q = 1) (hb : d92314 q = 1) : d93952 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d93952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77092 q = 1) (hb : d92314 q = 1) : d93953 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d93953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77093 q = 1) (hb : d92314 q = 1) : d93954 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d93954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77094 q = 1) (hb : d92314 q = 1) : d93955 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77094, d93955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11368 (p : Pattern) (ha : d77100 p = 1) (hb : d92317 p = 1) : d93961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77095 q = 1) (hb : d92314 q = 1) : d93956 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11367 q ha hb
    | true =>
      simp only [d77095, d93956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77096 q = 1) (hb : d92314 q = 1) : d93957 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d93957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92316 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77097 q = 1) (hb : d92317 q = 1) : d93958 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d92317, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d92317, d93958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77098 q = 1) (hb : d92317 q = 1) : d93959 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77098, d93959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77099 q = 1) (hb : d92317 q = 1) : d93960 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77099, d93960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d77100 q = 1) (hb : d92317 q = 1) : d93961 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77100, d93961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11369 (p : Pattern) (ha : d77106 p = 1) (hb : d92317 p = 1) : d93967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d92317 q = 1) : d93962 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11368 q ha hb
    | true =>
      simp only [d77101, d93962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d92317 q = 1) : d93963 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d93963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d92317 q = 1) : d93964 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d93964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d92317 q = 1) : d93965 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d93965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d92317 q = 1) : d93966 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d93966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d92317 q = 1) : d93967 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d93967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11370 (p : Pattern) (ha : d77112 p = 1) (hb : d92317 p = 1) : d93973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d92317 q = 1) : d93968 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11369 q ha hb
    | true =>
      simp only [d77107, d93968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d92317 q = 1) : d93969 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d93969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d92317 q = 1) : d93970 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d93970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d92317 q = 1) : d93971 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d93971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d92317 q = 1) : d93972 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d93972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d92317 q = 1) : d93973 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d93973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11371 (p : Pattern) (ha : d6739 p = 1) (hb : d81527 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d6738 q = 1) (hb : d81526 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6738, d81526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6738, d81526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6739 q = 1) (hb : d81527 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6739, d81527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6739, d81527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11372 (p : Pattern) (ha : d8334 p = 1) (hb : d92321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8331 q = 1) (hb : d92318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8332 q = 1) (hb : d92319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8333 q = 1) (hb : d92320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d92320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8333, d92320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8334 q = 1) (hb : d92321 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d92321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d92321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11373 (p : Pattern) (ha : d92327 p = 1) (hb : d93275 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
    | true =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d93271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d93272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d93273 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d93274 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92327 q = 1) (hb : d93275 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92327, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92327, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11374 (p : Pattern) (ha : d8355 p = 1) (hb : d92328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8331 q = 1) (hb : d92318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8332 q = 1) (hb : d92319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8333 q = 1) (hb : d92320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d92320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8333, d92320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8355 q = 1) (hb : d92328 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d92328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8355, d92328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11375 (p : Pattern) (ha : d92334 p = 1) (hb : d93281 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
    | true =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d93271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d93272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d93273 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d93274 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d92329 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11374 q hb ha
    | true =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92330 q = 1) (hb : d93277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92330, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d92331 q = 1) (hb : d93278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92331, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92332 q = 1) (hb : d93279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92332, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d92332, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92333 q = 1) (hb : d93280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92333, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d92333, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92334 q = 1) (hb : d93281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92334, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92334, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11376 (p : Pattern) (ha : d92341 p = 1) (hb : d93288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92329 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11374 q hb ha
    | true =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92330 q = 1) (hb : d93277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92330, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d92331 q = 1) (hb : d93278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92331, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92339 q = 1) (hb : d93286 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92339, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92339, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92340 q = 1) (hb : d93287 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92340, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92340, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92341 q = 1) (hb : d93288 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92341, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92341, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11377 (p : Pattern) (ha : d6772 p = 1) (hb : d81560 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d6771 q = 1) (hb : d81559 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6771, d81559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6771, d81559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6772 q = 1) (hb : d81560 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6772, d81560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6772, d81560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11378 (p : Pattern) (ha : d8398 p = 1) (hb : d92350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d81561 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11377 q ha hb
    | true =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d81562 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8395 q = 1) (hb : d92347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d92347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d92347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8396 q = 1) (hb : d92348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d92348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8396, d92348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8397 q = 1) (hb : d92349 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d92349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8397, d92349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8398 q = 1) (hb : d92350 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d92350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8398, d92350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11379 (p : Pattern) (ha : d92356 p = 1) (hb : d93299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92351 q = 1) (hb : d93294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11378 q hb ha
    | true =>
      simp only [d92351, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92352 q = 1) (hb : d93295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92352, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92352, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d92353 q = 1) (hb : d93296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92353, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92353, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92354 q = 1) (hb : d93297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92354, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92354, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92355 q = 1) (hb : d93298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92355, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92355, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92356 q = 1) (hb : d93299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92356, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92356, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11380 (p : Pattern) (ha : d92362 p = 1) (hb : d93305 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d92335 q = 1) (hb : d93282 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92335, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11373 q ha hb
    | true =>
      simp only [d92335, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11375 q ha hb
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
  have h8 (q : Pattern) (ha : d92336 q = 1) (hb : d93283 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92336, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92336, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d92337 q = 1) (hb : d93284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92337, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92337, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92338 q = 1) (hb : d93285 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92338, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d92338, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92342 q = 1) (hb : d93289 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92342, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92342, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11376 q ha hb
  have h12 (q : Pattern) (ha : d92343 q = 1) (hb : d93290 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92343, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92343, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92344 q = 1) (hb : d93291 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92344, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92344, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92345 q = 1) (hb : d93292 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92345, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92345, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92346 q = 1) (hb : d93293 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92346, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92346, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92357 q = 1) (hb : d93300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92357, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92357, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11379 q ha hb
  have h17 (q : Pattern) (ha : d92358 q = 1) (hb : d93301 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92358, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92358, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d92359 q = 1) (hb : d93302 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92359, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92359, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92360 q = 1) (hb : d93303 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92360, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d92360, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d92361 q = 1) (hb : d93304 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92361, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92361, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92362 q = 1) (hb : d93305 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92362, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92362, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro11381 (p : Pattern) (ha : d92372 p = 1) (hb : d93315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
    | true =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92372 q = 1) (hb : d93315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92372, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92372, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11382 (p : Pattern) (ha : d92379 p = 1) (hb : d93322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
    | true =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92329 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11374 q hb ha
    | true =>
      simp only [d92329, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d92375 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92375, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92375, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92376 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92376, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92376, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92377 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92377, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92377, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92378 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92378, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92378, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92379 q = 1) (hb : d93322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92379, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92379, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11383 (p : Pattern) (ha : d8334 p = 1) (hb : d92408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d92405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d92406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d92407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8334 q = 1) (hb : d92408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d92408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d92408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11384 (p : Pattern) (ha : d8313 p = 1) (hb : d92396 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6797 q = 1) (hb : d81585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d475 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8312 q = 1) (hb : d92395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8312, d92395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8312, d92395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8313 q = 1) (hb : d92396 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8313, d92396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8313, d92396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11385 (p : Pattern) (ha : d8479 p = 1) (hb : d92402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92399 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d92400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, d92400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8478 q = 1) (hb : d92401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d92401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8478, d92401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8479 q = 1) (hb : d92402 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d92402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d92402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11386 (p : Pattern) (ha : d92384 p = 1) (hb : d93327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8331 q = 1) (hb : d92318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8332 q = 1) (hb : d92319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92383 q = 1) (hb : d93326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92384 q = 1) (hb : d93327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92384, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92384, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11387 (p : Pattern) (ha : d92391 p = 1) (hb : d93334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8331 q = 1) (hb : d92318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92389 q = 1) (hb : d93332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92390 q = 1) (hb : d93333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92390, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92391 q = 1) (hb : d93334 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92391, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92391, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11388 (p : Pattern) (ha : d92414 p = 1) (hb : d93343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d93328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11386 q ha hb
    | true =>
      simp only [d92385, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d93329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d93330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d93331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d93335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11387 q ha hb
    | true =>
      simp only [d92392, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d93336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d93337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d93338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11385 q hb ha
    | true =>
      simp only [d92403, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d93339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8335 q = 1) (hb : d92409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11383 q ha hb
    | true =>
      simp only [d8335, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8336 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d92410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8336, d92410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d93340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d93341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d93342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92414 q = 1) (hb : d93343 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11389 (p : Pattern) (ha : d8355 p = 1) (hb : d92427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d92405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d92406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d92406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d92407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d92407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8355 q = 1) (hb : d92427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d92427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8355, d92427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11390 (p : Pattern) (ha : d8501 p = 1) (hb : d92424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92399 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d92400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, d92400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8478 q = 1) (hb : d92401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d92401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8478, d92401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8501 q = 1) (hb : d92424 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d92424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8501, d92424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11391 (p : Pattern) (ha : d92415 p = 1) (hb : d93344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8331 q = 1) (hb : d92318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8332 q = 1) (hb : d92319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8332, d92319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92383 q = 1) (hb : d93326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92415 q = 1) (hb : d93344 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92415, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92415, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11392 (p : Pattern) (ha : d92420 p = 1) (hb : d93349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d81528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11371 q ha hb
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d81529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8331 q = 1) (hb : d92318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d92318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92389 q = 1) (hb : d93332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92390 q = 1) (hb : d93333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92390, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92420 q = 1) (hb : d93349 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92420, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92420, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11393 (p : Pattern) (ha : d92433 p = 1) (hb : d93358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d93328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11386 q ha hb
    | true =>
      simp only [d92385, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d93329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d93330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d93331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d93335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11387 q ha hb
    | true =>
      simp only [d92392, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d93336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d93337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d93338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11385 q hb ha
    | true =>
      simp only [d92403, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d93339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8335 q = 1) (hb : d92409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11383 q ha hb
    | true =>
      simp only [d8335, d92409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8336 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d92410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8336, d92410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d93340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d93341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d93342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92416 q = 1) (hb : d93345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92416, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11391 q ha hb
    | true =>
      simp only [d92416, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d92417 q = 1) (hb : d93346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92417, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92417, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92418 q = 1) (hb : d93347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92418, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92418, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92419 q = 1) (hb : d93348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92419, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92419, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92421 q = 1) (hb : d93350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92421, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11392 q ha hb
    | true =>
      simp only [d92421, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d92422 q = 1) (hb : d93351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92422, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92422, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92423 q = 1) (hb : d93352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92423, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92423, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92425 q = 1) (hb : d93353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11390 q hb ha
    | true =>
      simp only [d92425, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11374 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92426 q = 1) (hb : d93354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92426, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8356 q = 1) (hb : d92428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11389 q ha hb
    | true =>
      simp only [d8356, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8357 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d92429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8357, d92429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d92430 q = 1) (hb : d93355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92430, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92431 q = 1) (hb : d93356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92431, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92432 q = 1) (hb : d93357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92432, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92433 q = 1) (hb : d93358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92433, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11394 (p : Pattern) (ha : d92435 p = 1) (hb : d93360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11372 q hb ha
    | true =>
      simp only [d92322, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d92435 q = 1) (hb : d93360 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92435, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92435, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11395 (p : Pattern) (ha : d92442 p = 1) (hb : d93367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92425 q = 1) (hb : d93353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11390 q hb ha
    | true =>
      simp only [d92425, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11374 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92426 q = 1) (hb : d93354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92426, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8356 q = 1) (hb : d92428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11389 q ha hb
    | true =>
      simp only [d8356, d92428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8357 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d92429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8357, d92429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92430 q = 1) (hb : d93355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92430, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92440 q = 1) (hb : d93365 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92440, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92440, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92441 q = 1) (hb : d93366 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92441, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92441, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92442 q = 1) (hb : d93367 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92442, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92442, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11396 (p : Pattern) (ha : d8398 p = 1) (hb : d92461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d81561 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11377 q ha hb
    | true =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d81562 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d81562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8395 q = 1) (hb : d92458 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d92458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d92458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8396 q = 1) (hb : d92459 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d92459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8396, d92459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8397 q = 1) (hb : d92460 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d92460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8397, d92460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8398 q = 1) (hb : d92461 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d92461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8398, d92461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11397 (p : Pattern) (ha : d8377 p = 1) (hb : d92449 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6843 q = 1) (hb : d81631 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d673 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8376 q = 1) (hb : d92448 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8376, d92448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8376, d92448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8377 q = 1) (hb : d92449 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8377, d92449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8377, d92449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11398 (p : Pattern) (ha : d8555 p = 1) (hb : d92455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d92450 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d92450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11397 q ha hb
    | true =>
      simp only [d8378, d92450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d92451 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d92451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d92451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81562 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8552 q = 1) (hb : d92452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d92452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d92452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8553 q = 1) (hb : d92453 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d92453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8553, d92453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8554 q = 1) (hb : d92454 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d92454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8554, d92454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8555 q = 1) (hb : d92455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d92455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8555, d92455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11399 (p : Pattern) (ha : d92467 p = 1) (hb : d93378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92456 q = 1) (hb : d93373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92456, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11398 q hb ha
    | true =>
      simp only [d92456, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11378 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92457 q = 1) (hb : d93374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92457, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92457, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8399 q = 1) (hb : d92462 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d92462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11396 q ha hb
    | true =>
      simp only [d8399, d92462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8400 q = 1) (hb : d92463 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d92463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8400, d92463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92464 q = 1) (hb : d93375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92464, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92464, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92465 q = 1) (hb : d93376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92465, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92465, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92466 q = 1) (hb : d93377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92466, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92466, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92467 q = 1) (hb : d93378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92467, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92467, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11400 (p : Pattern) (ha : d92473 p = 1) (hb : d93384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92373 q = 1) (hb : d93316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92373, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92373, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11381 q ha hb
  have h2 (q : Pattern) (ha : d92374 q = 1) (hb : d93317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92374, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92374, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92380 q = 1) (hb : d93323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92380, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11381 q ha hb
    | true =>
      simp only [d92380, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11382 q ha hb
  have h4 (q : Pattern) (ha : d92381 q = 1) (hb : d93324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92381, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92381, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92382 q = 1) (hb : d93325 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92382, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92382, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92434 q = 1) (hb : d93359 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92434, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11388 q ha hb
    | true =>
      simp only [d92434, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11393 q ha hb
  have h7 (q : Pattern) (ha : d92436 q = 1) (hb : d93361 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92436, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11394 q ha hb
    | true =>
      simp only [d92436, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d92437 q = 1) (hb : d93362 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92437, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92437, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92438 q = 1) (hb : d93363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92438, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92438, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92439 q = 1) (hb : d93364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92439, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92439, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92443 q = 1) (hb : d93368 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92443, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92443, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11395 q ha hb
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
  have h13 (q : Pattern) (ha : d92444 q = 1) (hb : d93369 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92444, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92444, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92445 q = 1) (hb : d93370 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92445, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92445, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92446 q = 1) (hb : d93371 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92446, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92446, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92447 q = 1) (hb : d93372 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92447, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92447, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92468 q = 1) (hb : d93379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92468, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92468, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11399 q ha hb
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
  have h19 (q : Pattern) (ha : d92469 q = 1) (hb : d93380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92469, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92469, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92470 q = 1) (hb : d93381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92470, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92470, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92471 q = 1) (hb : d93382 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92471, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92471, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92472 q = 1) (hb : d93383 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92472, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92472, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92473 q = 1) (hb : d93384 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92473, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92473, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11401 (p : Pattern) (ha : d92479 p = 1) (hb : d93390 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d92363 q = 1) (hb : d93306 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92363, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92363, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11380 q ha hb
  have h6 (q : Pattern) (ha : d92364 q = 1) (hb : d93307 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92364, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92364, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92365 q = 1) (hb : d93308 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92365, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92365, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92366 q = 1) (hb : d93309 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92366, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92366, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92367 q = 1) (hb : d93310 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92367, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92367, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92474 q = 1) (hb : d93385 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92474, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92474, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11400 q ha hb
  have h11 (q : Pattern) (ha : d92475 q = 1) (hb : d93386 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92475, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92475, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92476 q = 1) (hb : d93387 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92476, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92476, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92477 q = 1) (hb : d93388 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92477, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92477, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92478 q = 1) (hb : d93389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92478, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92478, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92479 q = 1) (hb : d93390 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92479, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92479, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11402 (p : Pattern) (ha : d8479 p = 1) (hb : d92483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d92481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8478 q = 1) (hb : d92482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d92482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8478, d92482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8479 q = 1) (hb : d92483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d92483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d92483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11403 (p : Pattern) (ha : d92489 p = 1) (hb : d93396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11402 q hb ha
    | true =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92489 q = 1) (hb : d93396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92489, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92489, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11404 (p : Pattern) (ha : d8501 p = 1) (hb : d92492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d92481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8478 q = 1) (hb : d92482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d92482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8478, d92482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8501 q = 1) (hb : d92492 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d92492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8501, d92492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11405 (p : Pattern) (ha : d92498 p = 1) (hb : d93404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11402 q hb ha
    | true =>
      simp only [d92484, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92493 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11404 q hb ha
    | true =>
      simp only [d92493, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h7 (q : Pattern) (ha : d92494 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92494, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92494, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92495 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92495, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92495, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92496 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92496, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92496, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92497 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92497, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92497, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92498 q = 1) (hb : d93404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92498, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92498, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11406 (p : Pattern) (ha : d8479 p = 1) (hb : d92532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d92529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d92530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d92530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d92531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d92531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d92531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8479 q = 1) (hb : d92532 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d92532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d92532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11407 (p : Pattern) (ha : d92503 p = 1) (hb : d93409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d92481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92502 q = 1) (hb : d93408 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92503 q = 1) (hb : d93409 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92503, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92503, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11408 (p : Pattern) (ha : d92510 p = 1) (hb : d93416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92508 q = 1) (hb : d93414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92509 q = 1) (hb : d93415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92509, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92510 q = 1) (hb : d93416 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92510, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92510, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11409 (p : Pattern) (ha : d8453 p = 1) (hb : d92516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d549, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8451 q = 1) (hb : d92514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8451, d92514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8451, d92514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h6 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6797 q = 1) (hb : d81585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8452 q = 1) (hb : d92515 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8452, d92515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8452, d92515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8453 q = 1) (hb : d92516 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8453, d92516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8453, d92516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11410 (p : Pattern) (ha : d92522 p = 1) (hb : d93423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d92517 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d92517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11409 q ha hb
    | true =>
      simp only [d8454, d92517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d92518 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d92518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d92518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81589 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92519 q = 1) (hb : d93420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92519, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92520 q = 1) (hb : d93421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92520, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92521 q = 1) (hb : d93422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92521, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92522 q = 1) (hb : d93423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92522, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92522, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11411 (p : Pattern) (ha : d6799 p = 1) (hb : d81587 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6797 q = 1) (hb : d81585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d81585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h9 (q : Pattern) (ha : d6798 q = 1) (hb : d81586 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6798, d81586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6798, d81586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6799 q = 1) (hb : d81587 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6799, d81587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6799, d81587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11412 (p : Pattern) (ha : d92526 p = 1) (hb : d93427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d81588 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11411 q ha hb
    | true =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d81589 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92523 q = 1) (hb : d93424 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92523, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92524 q = 1) (hb : d93425 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92524, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92525 q = 1) (hb : d93426 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92525, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92526 q = 1) (hb : d93427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92526, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92526, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11413 (p : Pattern) (ha : d92538 p = 1) (hb : d93433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d93410 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11407 q ha hb
    | true =>
      simp only [d92504, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d93411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d93412 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d93413 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d93417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11408 q ha hb
    | true =>
      simp only [d92511, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d93418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d93419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d93428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11410 q ha hb
    | true =>
      simp only [d92527, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11412 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d93429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8480 q = 1) (hb : d92533 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d92533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11406 q ha hb
    | true =>
      simp only [d8480, d92533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8481 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d92534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8481, d92534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d93430 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d93431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d93432 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92538 q = 1) (hb : d93433 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92538, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92538, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11414 (p : Pattern) (ha : d8501 p = 1) (hb : d92552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d92529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d92530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d92530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d92531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d92531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d92531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8501 q = 1) (hb : d92552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d92552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8501, d92552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11415 (p : Pattern) (ha : d92539 p = 1) (hb : d93434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8477 q = 1) (hb : d92481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8477, d92481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92502 q = 1) (hb : d93408 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92539 q = 1) (hb : d93434 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92539, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92539, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11416 (p : Pattern) (ha : d92544 p = 1) (hb : d93439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d92397 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11384 q ha hb
    | true =>
      simp only [d8314, d92397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d92398 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d92398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8476 q = 1) (hb : d92480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d92480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92508 q = 1) (hb : d93414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92509 q = 1) (hb : d93415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92509, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92544 q = 1) (hb : d93439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92544, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92544, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11417 (p : Pattern) (ha : d92548 p = 1) (hb : d93443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d92517 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d92517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11409 q ha hb
    | true =>
      simp only [d8454, d92517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d92518 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d92518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d92518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81589 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92519 q = 1) (hb : d93420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92519, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92520 q = 1) (hb : d93421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92520, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92521 q = 1) (hb : d93422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92521, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92548 q = 1) (hb : d93443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92548, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92548, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11418 (p : Pattern) (ha : d92549 p = 1) (hb : d93444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d81588 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11411 q ha hb
    | true =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d81589 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92523 q = 1) (hb : d93424 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92523, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92524 q = 1) (hb : d93425 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92524, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92525 q = 1) (hb : d93426 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92525, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92549 q = 1) (hb : d93444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92549, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92549, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11419 (p : Pattern) (ha : d92558 p = 1) (hb : d93450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d93410 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11407 q ha hb
    | true =>
      simp only [d92504, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q hb ha
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d93411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d93412 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d93413 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d93417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11408 q ha hb
    | true =>
      simp only [d92511, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q hb ha
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d93418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d93419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d93428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11410 q ha hb
    | true =>
      simp only [d92527, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11412 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d93429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8480 q = 1) (hb : d92533 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d92533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11406 q ha hb
    | true =>
      simp only [d8480, d92533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8481 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d92534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8481, d92534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d93430 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d93431 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d93432 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92540 q = 1) (hb : d93435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92540, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11415 q ha hb
    | true =>
      simp only [d92540, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q hb ha
  have h17 (q : Pattern) (ha : d92541 q = 1) (hb : d93436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92541, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92541, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92542 q = 1) (hb : d93437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92542, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92542, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92543 q = 1) (hb : d93438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92543, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92543, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92545 q = 1) (hb : d93440 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92545, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11416 q ha hb
    | true =>
      simp only [d92545, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q hb ha
  have h21 (q : Pattern) (ha : d92546 q = 1) (hb : d93441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92546, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92546, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92547 q = 1) (hb : d93442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92547, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92547, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92550 q = 1) (hb : d93445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11417 q ha hb
    | true =>
      simp only [d92550, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11418 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92551 q = 1) (hb : d93446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92551, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8502 q = 1) (hb : d92553 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d92553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11414 q ha hb
    | true =>
      simp only [d8502, d92553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8503 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d92554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8503, d92554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d92555 q = 1) (hb : d93447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92555, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92556 q = 1) (hb : d93448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92556, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92556, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92557 q = 1) (hb : d93449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92557, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92557, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92558 q = 1) (hb : d93450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92558, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92558, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11420 (p : Pattern) (ha : d92565 p = 1) (hb : d93457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92560 q = 1) (hb : d93452 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92560, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11412 q ha hb
    | true =>
      simp only [d92560, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d92561 q = 1) (hb : d93453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92561, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92561, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92562 q = 1) (hb : d93454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92562, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92562, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92563 q = 1) (hb : d93455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92563, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92563, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92564 q = 1) (hb : d93456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92564, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92564, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d92565 q = 1) (hb : d93457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92565, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92565, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11421 (p : Pattern) (ha : d92572 p = 1) (hb : d93464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92550 q = 1) (hb : d93445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11417 q ha hb
    | true =>
      simp only [d92550, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11418 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92551 q = 1) (hb : d93446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92551, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8502 q = 1) (hb : d92553 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d92553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11414 q ha hb
    | true =>
      simp only [d8502, d92553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8503 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d92554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8503, d92554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92555 q = 1) (hb : d93447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92555, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92570 q = 1) (hb : d93462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92570, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92570, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92571 q = 1) (hb : d93463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92571, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92571, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92572 q = 1) (hb : d93464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92572, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92572, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11422 (p : Pattern) (ha : d8555 p = 1) (hb : d92601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d92450 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d92450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11397 q ha hb
    | true =>
      simp only [d8378, d92450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d92451 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d92451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d92451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8552 q = 1) (hb : d92598 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d92598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d92598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8553 q = 1) (hb : d92599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d92599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8553, d92599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8554 q = 1) (hb : d92600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d92600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8554, d92600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8555 q = 1) (hb : d92601 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d92601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8555, d92601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11423 (p : Pattern) (ha : d8529 p = 1) (hb : d92580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d665, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8527 q = 1) (hb : d92578 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8527, d92578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8527, d92578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h6 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6843 q = 1) (hb : d81631 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8528 q = 1) (hb : d92579 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8528, d92579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8528, d92579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8529 q = 1) (hb : d92580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8529, d92580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8529, d92580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11424 (p : Pattern) (ha : d92586 p = 1) (hb : d93473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8530 q = 1) (hb : d92581 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8530, d92581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11423 q ha hb
    | true =>
      simp only [d8530, d92581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8531 q = 1) (hb : d92582 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8531, d92582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8531, d92582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81635 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92583 q = 1) (hb : d93470 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92583, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92583, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92584 q = 1) (hb : d93471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92584, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92584, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92585 q = 1) (hb : d93472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92585, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92585, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92586 q = 1) (hb : d93473 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92586, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92586, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11425 (p : Pattern) (ha : d6845 p = 1) (hb : d81633 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6843 q = 1) (hb : d81631 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d81631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h9 (q : Pattern) (ha : d6844 q = 1) (hb : d81632 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6844, d81632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6844, d81632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6845 q = 1) (hb : d81633 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6845, d81633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6845, d81633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11426 (p : Pattern) (ha : d92590 p = 1) (hb : d93477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6846 q = 1) (hb : d81634 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d81634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11425 q ha hb
    | true =>
      simp only [d6846, d81634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6847 q = 1) (hb : d81635 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d81635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d81635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92587 q = 1) (hb : d93474 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92587, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92587, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92588 q = 1) (hb : d93475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92588, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92588, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92589 q = 1) (hb : d93476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92589, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92589, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92590 q = 1) (hb : d93477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92590, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92590, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11427 (p : Pattern) (ha : d92607 p = 1) (hb : d93483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92591 q = 1) (hb : d93478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92591, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11424 q ha hb
    | true =>
      simp only [d92591, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11426 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92597 q = 1) (hb : d93479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92597, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92597, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8556 q = 1) (hb : d92602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8556, d92602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11422 q ha hb
    | true =>
      simp only [d8556, d92602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8557 q = 1) (hb : d92603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8557, d92603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8557, d92603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92604 q = 1) (hb : d93480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92604, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92604, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92605 q = 1) (hb : d93481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92605, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92605, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92606 q = 1) (hb : d93482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92606, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92606, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92607 q = 1) (hb : d93483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92607, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92607, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11428 (p : Pattern) (ha : d92613 p = 1) (hb : d93489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92490 q = 1) (hb : d93397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92490, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92490, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11403 q ha hb
  have h2 (q : Pattern) (ha : d92491 q = 1) (hb : d93398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92491, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92491, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92499 q = 1) (hb : d93405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92499, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11403 q ha hb
    | true =>
      simp only [d92499, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11405 q ha hb
  have h4 (q : Pattern) (ha : d92500 q = 1) (hb : d93406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92500, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92500, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92501 q = 1) (hb : d93407 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92501, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92501, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92559 q = 1) (hb : d93451 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92559, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11413 q ha hb
    | true =>
      simp only [d92559, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11419 q ha hb
  have h7 (q : Pattern) (ha : d92566 q = 1) (hb : d93458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92566, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11420 q ha hb
    | true =>
      simp only [d92566, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q hb ha
  have h8 (q : Pattern) (ha : d92567 q = 1) (hb : d93459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92567, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92567, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92568 q = 1) (hb : d93460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92568, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92568, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92569 q = 1) (hb : d93461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92569, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92569, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92573 q = 1) (hb : d93465 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92573, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92573, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11421 q ha hb
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
  have h13 (q : Pattern) (ha : d92574 q = 1) (hb : d93466 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92574, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92574, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92575 q = 1) (hb : d93467 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92575, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92575, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92576 q = 1) (hb : d93468 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92576, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92576, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92577 q = 1) (hb : d93469 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92577, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92577, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92608 q = 1) (hb : d93484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92608, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92608, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11427 q ha hb
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
  have h19 (q : Pattern) (ha : d92609 q = 1) (hb : d93485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92609, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92609, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92610 q = 1) (hb : d93486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92610, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92610, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92611 q = 1) (hb : d93487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92611, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92611, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92612 q = 1) (hb : d93488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92612, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92612, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92613 q = 1) (hb : d93489 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92613, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92613, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11429 (p : Pattern) (ha : d92619 p = 1) (hb : d93495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92614 q = 1) (hb : d93490 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92614, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92614, d93490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11428 q ha hb
  have h2 (q : Pattern) (ha : d92615 q = 1) (hb : d93491 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92615, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92615, d93491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92616 q = 1) (hb : d93492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92616, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92616, d93492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92617 q = 1) (hb : d93493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92617, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92617, d93493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92618 q = 1) (hb : d93494 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92618, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92618, d93494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92619 q = 1) (hb : d93495 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92619, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92619, d93495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11430 (p : Pattern) (ha : d8576 p = 1) (hb : d92622 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6875 q = 1) (hb : d81663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d763 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d763, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h6 (q : Pattern) (ha : d764 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d765 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d767, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8575 q = 1) (hb : d92621 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8575, d92621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8575, d92621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8576 q = 1) (hb : d92622 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8576, d92622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8576, d92622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11431 (p : Pattern) (ha : d8641 p = 1) (hb : d92628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d92625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8639 q = 1) (hb : d92626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8640 q = 1) (hb : d92627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d92627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8640, d92627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8641 q = 1) (hb : d92628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8641, d92628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8641, d92628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11432 (p : Pattern) (ha : d92634 p = 1) (hb : d93502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92629 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11431 q hb ha
    | true =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d92630 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92630, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92630, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92631 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92631, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92631, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92632 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92632, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92632, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92633 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92633, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92633, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92634 q = 1) (hb : d93502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92634, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92634, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11433 (p : Pattern) (ha : d8663 p = 1) (hb : d92637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d92625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8639 q = 1) (hb : d92626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8640 q = 1) (hb : d92627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d92627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8640, d92627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8663 q = 1) (hb : d92637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, d92637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8663, d92637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11434 (p : Pattern) (ha : d92643 p = 1) (hb : d93510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92629 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11431 q hb ha
    | true =>
      simp only [d92629, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d92630 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92630, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92630, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92631 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92631, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92631, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92632 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92632, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92632, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92633 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92633, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92633, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92638 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11433 q hb ha
    | true =>
      simp only [d92638, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h7 (q : Pattern) (ha : d92639 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92639, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92639, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92640 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92640, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92640, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92641 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92641, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92641, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92642 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92642, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92642, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92643 q = 1) (hb : d93510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92643, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92643, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11435 (p : Pattern) (ha : d8641 p = 1) (hb : d92677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d92674 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d92675 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d92675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d92675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d92676 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d92676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d92676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8641 q = 1) (hb : d92677 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8641, d92677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8641, d92677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11436 (p : Pattern) (ha : d92648 p = 1) (hb : d93515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d92625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8639 q = 1) (hb : d92626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92647 q = 1) (hb : d93514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92647, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92647, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92648 q = 1) (hb : d93515 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92648, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92648, d93515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11437 (p : Pattern) (ha : d92655 p = 1) (hb : d93522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d92625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92653 q = 1) (hb : d93520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92653, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92653, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92654 q = 1) (hb : d93521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92654, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92654, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92655 q = 1) (hb : d93522 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92655, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92655, d93522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11438 (p : Pattern) (ha : d8615 p = 1) (hb : d92661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d840 q = 1) (hb : d52517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro123 q ha hb
    | true =>
      simp only [d840, d52517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
  have h2 (q : Pattern) (ha : d841 q = 1) (hb : d52518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d52518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d842 q = 1) (hb : d52519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d52519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8613 q = 1) (hb : d92659 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8613, d92659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8613, d92659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d759 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h6 (q : Pattern) (ha : d760 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d761 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6875 q = 1) (hb : d81663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8614 q = 1) (hb : d92660 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8614, d92660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8614, d92660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8615 q = 1) (hb : d92661 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8615, d92661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8615, d92661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11439 (p : Pattern) (ha : d92667 p = 1) (hb : d93529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d92662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d92662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11438 q ha hb
    | true =>
      simp only [d8616, d92662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d92663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d92663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d92663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81667 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92664 q = 1) (hb : d93526 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92664, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92664, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92665 q = 1) (hb : d93527 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92665, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92665, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92666 q = 1) (hb : d93528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92666, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92666, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92667 q = 1) (hb : d93529 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92667, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92667, d93529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11440 (p : Pattern) (ha : d6877 p = 1) (hb : d81665 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6875 q = 1) (hb : d81663 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d81663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4914 q = 1) (hb : d69007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q ha hb
    | true =>
      simp only [d4914, d69007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h6 (q : Pattern) (ha : d4915 q = 1) (hb : d69008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d69008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4916 q = 1) (hb : d69009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d69009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4917 q = 1) (hb : d69010 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d69010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4917, d69010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6876 q = 1) (hb : d81664 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6876, d81664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6876, d81664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6877 q = 1) (hb : d81665 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6877, d81665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6877, d81665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11441 (p : Pattern) (ha : d92671 p = 1) (hb : d93533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d81666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11440 q ha hb
    | true =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d81667 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92668 q = 1) (hb : d93530 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92668, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92668, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92669 q = 1) (hb : d93531 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92669, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92669, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92670 q = 1) (hb : d93532 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92670, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92670, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92671 q = 1) (hb : d93533 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92671, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92671, d93533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11442 (p : Pattern) (ha : d92683 p = 1) (hb : d93539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92649 q = 1) (hb : d93516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92649, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11436 q ha hb
    | true =>
      simp only [d92649, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d92650 q = 1) (hb : d93517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92650, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92650, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92651 q = 1) (hb : d93518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92651, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92651, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92652 q = 1) (hb : d93519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92652, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92652, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92656 q = 1) (hb : d93523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92656, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11437 q ha hb
    | true =>
      simp only [d92656, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d92657 q = 1) (hb : d93524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92657, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92657, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92658 q = 1) (hb : d93525 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92658, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92658, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92672 q = 1) (hb : d93534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92672, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11439 q ha hb
    | true =>
      simp only [d92672, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11441 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92629 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92673 q = 1) (hb : d93535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92673, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8642 q = 1) (hb : d92678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d92678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11435 q ha hb
    | true =>
      simp only [d8642, d92678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8643 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d92679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8643, d92679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92680 q = 1) (hb : d93536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92680, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92681 q = 1) (hb : d93537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92681, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92682 q = 1) (hb : d93538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92682, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92683 q = 1) (hb : d93539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92683, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92683, d93539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11443 (p : Pattern) (ha : d8663 p = 1) (hb : d92697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d92674 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d92675 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d92675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d92675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d92676 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d92676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d92676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8663 q = 1) (hb : d92697 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, d92697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8663, d92697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11444 (p : Pattern) (ha : d92684 p = 1) (hb : d93540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d92625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8639 q = 1) (hb : d92626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8639, d92626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92647 q = 1) (hb : d93514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92647, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92647, d93514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92684 q = 1) (hb : d93540 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92684, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92684, d93540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11445 (p : Pattern) (ha : d92689 p = 1) (hb : d93545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d92623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11430 q ha hb
    | true =>
      simp only [d8577, d92623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d92624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d92624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8638 q = 1) (hb : d92625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d92625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92653 q = 1) (hb : d93520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92653, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92653, d93520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92654 q = 1) (hb : d93521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92654, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92654, d93521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92689 q = 1) (hb : d93545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92689, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92689, d93545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11446 (p : Pattern) (ha : d92693 p = 1) (hb : d93549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d92662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d92662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11438 q ha hb
    | true =>
      simp only [d8616, d92662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d92663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d92663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d92663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81667 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92664 q = 1) (hb : d93526 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92664, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92664, d93526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92665 q = 1) (hb : d93527 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92665, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92665, d93527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92666 q = 1) (hb : d93528 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92666, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92666, d93528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92693 q = 1) (hb : d93549 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92693, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92693, d93549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11447 (p : Pattern) (ha : d92694 p = 1) (hb : d93550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d81666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11440 q ha hb
    | true =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d81667 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92668 q = 1) (hb : d93530 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92668, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92668, d93530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92669 q = 1) (hb : d93531 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92669, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92669, d93531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92670 q = 1) (hb : d93532 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92670, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92670, d93532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92694 q = 1) (hb : d93550 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92694, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92694, d93550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11448 (p : Pattern) (ha : d92703 p = 1) (hb : d93556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92649 q = 1) (hb : d93516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92649, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11436 q ha hb
    | true =>
      simp only [d92649, d93516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q hb ha
  have h2 (q : Pattern) (ha : d92650 q = 1) (hb : d93517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92650, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92650, d93517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92651 q = 1) (hb : d93518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92651, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92651, d93518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92652 q = 1) (hb : d93519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92652, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92652, d93519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92656 q = 1) (hb : d93523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92656, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11437 q ha hb
    | true =>
      simp only [d92656, d93523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q hb ha
  have h6 (q : Pattern) (ha : d92657 q = 1) (hb : d93524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92657, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92657, d93524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92658 q = 1) (hb : d93525 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92658, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92658, d93525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92672 q = 1) (hb : d93534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92672, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11439 q ha hb
    | true =>
      simp only [d92672, d93534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11441 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92629 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92673 q = 1) (hb : d93535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92673, d93535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8642 q = 1) (hb : d92678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d92678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11435 q ha hb
    | true =>
      simp only [d8642, d92678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8643 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d92679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8643, d92679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92680 q = 1) (hb : d93536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92680, d93536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92681 q = 1) (hb : d93537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92681, d93537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92682 q = 1) (hb : d93538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92682, d93538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92685 q = 1) (hb : d93541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92685, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11444 q ha hb
    | true =>
      simp only [d92685, d93541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q hb ha
  have h17 (q : Pattern) (ha : d92686 q = 1) (hb : d93542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92686, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92686, d93542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92687 q = 1) (hb : d93543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92687, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92687, d93543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92688 q = 1) (hb : d93544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92688, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92688, d93544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92690 q = 1) (hb : d93546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92690, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11445 q ha hb
    | true =>
      simp only [d92690, d93546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q hb ha
  have h21 (q : Pattern) (ha : d92691 q = 1) (hb : d93547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92691, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92691, d93547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92692 q = 1) (hb : d93548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92692, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92692, d93548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92695 q = 1) (hb : d93551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92695, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11446 q ha hb
    | true =>
      simp only [d92695, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11447 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92638 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92696 q = 1) (hb : d93552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92696, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8664 q = 1) (hb : d92698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d92698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11443 q ha hb
    | true =>
      simp only [d8664, d92698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8665 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d92699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8665, d92699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d92700 q = 1) (hb : d93553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92700, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92701 q = 1) (hb : d93554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92701, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92701, d93554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92702 q = 1) (hb : d93555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92702, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92702, d93555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92703 q = 1) (hb : d93556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92703, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92703, d93556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11449 (p : Pattern) (ha : d92710 p = 1) (hb : d93563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92705 q = 1) (hb : d93558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92705, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11441 q ha hb
    | true =>
      simp only [d92705, d93558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h2 (q : Pattern) (ha : d92706 q = 1) (hb : d93559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92706, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92706, d93559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92707 q = 1) (hb : d93560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92707, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92707, d93560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92708 q = 1) (hb : d93561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92708, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92708, d93561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92709 q = 1) (hb : d93562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92709, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92709, d93562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d92710 q = 1) (hb : d93563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92710, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92710, d93563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11450 (p : Pattern) (ha : d92717 p = 1) (hb : d93570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92695 q = 1) (hb : d93551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92695, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11446 q ha hb
    | true =>
      simp only [d92695, d93551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11447 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92638 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92696 q = 1) (hb : d93552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92696, d93552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8664 q = 1) (hb : d92698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d92698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11443 q ha hb
    | true =>
      simp only [d8664, d92698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8665 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d92699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8665, d92699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92700 q = 1) (hb : d93553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92700, d93553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92715 q = 1) (hb : d93568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92715, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92715, d93568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92716 q = 1) (hb : d93569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92716, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92716, d93569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92717 q = 1) (hb : d93570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92717, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92717, d93570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11451 (p : Pattern) (ha : d8715 p = 1) (hb : d92738 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6921 q = 1) (hb : d81709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h6 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8714 q = 1) (hb : d92737 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8714, d92737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8714, d92737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8715 q = 1) (hb : d92738 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8715, d92738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8715, d92738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11452 (p : Pattern) (ha : d8721 p = 1) (hb : d92750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d92739 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d92739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11451 q ha hb
    | true =>
      simp only [d8716, d92739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d92740 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d92740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d92740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8718 q = 1) (hb : d92747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, d92747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, d92747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8719 q = 1) (hb : d92748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, d92748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8719, d92748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8720 q = 1) (hb : d92749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, d92749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8720, d92749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8721 q = 1) (hb : d92750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, d92750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8721, d92750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11453 (p : Pattern) (ha : d8691 p = 1) (hb : d92725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d52596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro127 q ha hb
    | true =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d52597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d52598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8689 q = 1) (hb : d92723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8689, d92723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8689, d92723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h6 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6921 q = 1) (hb : d81709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8690 q = 1) (hb : d92724 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8690, d92724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8690, d92724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8691 q = 1) (hb : d92725 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8691, d92725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8691, d92725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11454 (p : Pattern) (ha : d92731 p = 1) (hb : d93579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8692 q = 1) (hb : d92726 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8692, d92726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11453 q ha hb
    | true =>
      simp only [d8692, d92726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d92727 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d92727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d92727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81713 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92728 q = 1) (hb : d93576 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92728, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92728, d93576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92729 q = 1) (hb : d93577 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92729, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92729, d93577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92730 q = 1) (hb : d93578 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92730, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92730, d93578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92731 q = 1) (hb : d93579 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92731, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92731, d93579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11455 (p : Pattern) (ha : d6923 p = 1) (hb : d81711 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6921 q = 1) (hb : d81709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d81709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6211 q = 1) (hb : d75962 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q ha hb
    | true =>
      simp only [d6211, d75962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h6 (q : Pattern) (ha : d6212 q = 1) (hb : d75963 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d75963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6213 q = 1) (hb : d75964 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d75964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6214 q = 1) (hb : d75965 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6214, d75965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6922 q = 1) (hb : d81710 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6922, d81710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6922, d81710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6923 q = 1) (hb : d81711 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6923, d81711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6923, d81711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11456 (p : Pattern) (ha : d92735 p = 1) (hb : d93583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6924 q = 1) (hb : d81712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d81712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11455 q ha hb
    | true =>
      simp only [d6924, d81712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d81713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d81713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d81713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92732 q = 1) (hb : d93580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92732, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92732, d93580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92733 q = 1) (hb : d93581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92733, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92733, d93581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92734 q = 1) (hb : d93582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92734, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92734, d93582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92735 q = 1) (hb : d93583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92735, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92735, d93583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11457 (p : Pattern) (ha : d92756 p = 1) (hb : d93589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92736 q = 1) (hb : d93584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92736, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11454 q ha hb
    | true =>
      simp only [d92736, d93584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11456 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92746 q = 1) (hb : d93585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92746, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92746, d93585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8722 q = 1) (hb : d92751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, d92751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11452 q ha hb
    | true =>
      simp only [d8722, d92751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8723 q = 1) (hb : d92752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, d92752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8723, d92752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92753 q = 1) (hb : d93586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92753, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92753, d93586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92754 q = 1) (hb : d93587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92754, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92754, d93587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92755 q = 1) (hb : d93588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92755, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92755, d93588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92756 q = 1) (hb : d93589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92756, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92756, d93589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11458 (p : Pattern) (ha : d92762 p = 1) (hb : d93595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92635 q = 1) (hb : d93503 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92635, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92635, d93503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11432 q ha hb
  have h2 (q : Pattern) (ha : d92636 q = 1) (hb : d93504 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92636, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92636, d93504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92644 q = 1) (hb : d93511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92644, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11432 q ha hb
    | true =>
      simp only [d92644, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11434 q ha hb
  have h4 (q : Pattern) (ha : d92645 q = 1) (hb : d93512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92645, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92645, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92646 q = 1) (hb : d93513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92646, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92646, d93513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92704 q = 1) (hb : d93557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92704, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11442 q ha hb
    | true =>
      simp only [d92704, d93557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11448 q ha hb
  have h7 (q : Pattern) (ha : d92711 q = 1) (hb : d93564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92711, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11449 q ha hb
    | true =>
      simp only [d92711, d93564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q hb ha
  have h8 (q : Pattern) (ha : d92712 q = 1) (hb : d93565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92712, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92712, d93565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92713 q = 1) (hb : d93566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92713, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92713, d93566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92714 q = 1) (hb : d93567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92714, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92714, d93567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92718 q = 1) (hb : d93571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92718, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92718, d93571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11450 q ha hb
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
  have h13 (q : Pattern) (ha : d92719 q = 1) (hb : d93572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92719, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92719, d93572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92720 q = 1) (hb : d93573 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92720, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92720, d93573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92721 q = 1) (hb : d93574 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92721, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92721, d93574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92722 q = 1) (hb : d93575 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92722, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92722, d93575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92757 q = 1) (hb : d93590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92757, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92757, d93590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11457 q ha hb
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
  have h19 (q : Pattern) (ha : d92758 q = 1) (hb : d93591 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92758, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92758, d93591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92759 q = 1) (hb : d93592 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92759, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92759, d93592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92760 q = 1) (hb : d93593 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92760, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92760, d93593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92761 q = 1) (hb : d93594 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92761, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92761, d93594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92762 q = 1) (hb : d93595 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92762, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92762, d93595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11459 (p : Pattern) (ha : d92768 p = 1) (hb : d93601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92763 q = 1) (hb : d93596 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92763, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92763, d93596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11458 q ha hb
  have h2 (q : Pattern) (ha : d92764 q = 1) (hb : d93597 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92764, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92764, d93597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92765 q = 1) (hb : d93598 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92765, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92765, d93598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92766 q = 1) (hb : d93599 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92766, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92766, d93599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92767 q = 1) (hb : d93600 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92767, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92767, d93600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92768 q = 1) (hb : d93601 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92768, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92768, d93601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11460 (p : Pattern) (ha : d8743 p = 1) (hb : d92772 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6954 q = 1) (hb : d81742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1142 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro155 q ha hb
  have h6 (q : Pattern) (ha : d1143 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1144 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1146 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1146, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8742 q = 1) (hb : d92771 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8742, d92771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8742, d92771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8743 q = 1) (hb : d92772 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8743, d92772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8743, d92772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11461 (p : Pattern) (ha : d8808 p = 1) (hb : d92778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d92775 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8806 q = 1) (hb : d92776 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8807 q = 1) (hb : d92777 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d92777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8807, d92777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8808 q = 1) (hb : d92778 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, d92778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, d92778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11462 (p : Pattern) (ha : d92784 p = 1) (hb : d93609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92779 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11461 q hb ha
    | true =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d92780 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92780, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92780, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92781 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92781, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92781, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92782 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92782, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92782, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92783 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92783, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92783, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92784 q = 1) (hb : d93609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92784, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92784, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11463 (p : Pattern) (ha : d8830 p = 1) (hb : d92787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d92775 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8806 q = 1) (hb : d92776 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8807 q = 1) (hb : d92777 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d92777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8807, d92777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8830 q = 1) (hb : d92787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, d92787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8830, d92787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11464 (p : Pattern) (ha : d92793 p = 1) (hb : d93617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92779 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11461 q hb ha
    | true =>
      simp only [d92779, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d92780 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92780, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92780, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92781 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92781, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92781, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92782 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92782, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92782, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92783 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92783, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92783, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92788 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11463 q hb ha
    | true =>
      simp only [d92788, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h7 (q : Pattern) (ha : d92789 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92789, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92789, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92790 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92790, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92790, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92791 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92791, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92791, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92792 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92792, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92792, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92793 q = 1) (hb : d93617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92793, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92793, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11465 (p : Pattern) (ha : d8808 p = 1) (hb : d92827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d92824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d92825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d92825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d92825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d92826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d92826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d92826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8808 q = 1) (hb : d92827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, d92827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, d92827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11466 (p : Pattern) (ha : d92798 p = 1) (hb : d93622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d92775 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8806 q = 1) (hb : d92776 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92797 q = 1) (hb : d93621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92797, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92797, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92798 q = 1) (hb : d93622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92798, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92798, d93622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11467 (p : Pattern) (ha : d92805 p = 1) (hb : d93629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d92775 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92803 q = 1) (hb : d93627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92803, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92803, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92804 q = 1) (hb : d93628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92804, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92804, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92805 q = 1) (hb : d93629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92805, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92805, d93629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11468 (p : Pattern) (ha : d8782 p = 1) (hb : d92811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d52797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro175 q ha hb
    | true =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d52798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d52799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8780 q = 1) (hb : d92809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8780, d92809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8780, d92809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1129 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
  have h6 (q : Pattern) (ha : d1130 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1131 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6954 q = 1) (hb : d81742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8781 q = 1) (hb : d92810 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8781, d92810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8781, d92810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8782 q = 1) (hb : d92811 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8782, d92811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8782, d92811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11469 (p : Pattern) (ha : d92817 p = 1) (hb : d93636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d92812 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d92812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11468 q ha hb
    | true =>
      simp only [d8783, d92812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d92813 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d92813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d92813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81746 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92814 q = 1) (hb : d93633 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92814, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92814, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92815 q = 1) (hb : d93634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92815, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92815, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92816 q = 1) (hb : d93635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92816, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92816, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92817 q = 1) (hb : d93636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92817, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92817, d93636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11470 (p : Pattern) (ha : d6956 p = 1) (hb : d81744 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d6954 q = 1) (hb : d81742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d81742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5024 q = 1) (hb : d69114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d69114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q ha hb
    | true =>
      simp only [d5024, d69114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7948 q ha hb
  have h6 (q : Pattern) (ha : d5025 q = 1) (hb : d69115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d69115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d69115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5026 q = 1) (hb : d69116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d69116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d69116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5027 q = 1) (hb : d69117 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d69117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5027, d69117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6955 q = 1) (hb : d81743 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6955, d81743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6955, d81743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6956 q = 1) (hb : d81744 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6956, d81744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6956, d81744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11471 (p : Pattern) (ha : d92821 p = 1) (hb : d93640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d81745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11470 q ha hb
    | true =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d81746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92818 q = 1) (hb : d93637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92818, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92818, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92819 q = 1) (hb : d93638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92819, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92819, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92820 q = 1) (hb : d93639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92820, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92820, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92821 q = 1) (hb : d93640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92821, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92821, d93640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11472 (p : Pattern) (ha : d92833 p = 1) (hb : d93646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92799 q = 1) (hb : d93623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92799, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11466 q ha hb
    | true =>
      simp only [d92799, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d92800 q = 1) (hb : d93624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92800, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92800, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92801 q = 1) (hb : d93625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92801, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92801, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92802 q = 1) (hb : d93626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92802, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92802, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92806 q = 1) (hb : d93630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92806, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11467 q ha hb
    | true =>
      simp only [d92806, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d92807 q = 1) (hb : d93631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92807, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92807, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92808 q = 1) (hb : d93632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92808, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92808, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92822 q = 1) (hb : d93641 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92822, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11469 q ha hb
    | true =>
      simp only [d92822, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11471 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92823 q = 1) (hb : d93642 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92823, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8809 q = 1) (hb : d92828 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d92828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11465 q ha hb
    | true =>
      simp only [d8809, d92828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d92829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8810, d92829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92830 q = 1) (hb : d93643 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92830, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92831 q = 1) (hb : d93644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92831, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92832 q = 1) (hb : d93645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92832, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92833 q = 1) (hb : d93646 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92833, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92833, d93646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro11473 (p : Pattern) (ha : d8830 p = 1) (hb : d92847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8805 q = 1) (hb : d92824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8806 q = 1) (hb : d92825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d92825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8806, d92825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8807 q = 1) (hb : d92826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8807, d92826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8807, d92826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8830 q = 1) (hb : d92847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8830, d92847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8830, d92847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11474 (p : Pattern) (ha : d92834 p = 1) (hb : d93647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d92775 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8806 q = 1) (hb : d92776 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8806, d92776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92797 q = 1) (hb : d93621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92797, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92797, d93621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92834 q = 1) (hb : d93647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92834, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92834, d93647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11475 (p : Pattern) (ha : d92839 p = 1) (hb : d93652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8744 q = 1) (hb : d92773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11460 q ha hb
    | true =>
      simp only [d8744, d92773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8745 q = 1) (hb : d92774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8745, d92774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8805 q = 1) (hb : d92775 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8805, d92775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92803 q = 1) (hb : d93627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92803, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92803, d93627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92804 q = 1) (hb : d93628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92804, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92804, d93628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92839 q = 1) (hb : d93652 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92839, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92839, d93652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11476 (p : Pattern) (ha : d92843 p = 1) (hb : d93656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d92812 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d92812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11468 q ha hb
    | true =>
      simp only [d8783, d92812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d92813 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d92813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d92813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81746 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92814 q = 1) (hb : d93633 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92814, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92814, d93633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92815 q = 1) (hb : d93634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92815, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92815, d93634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92816 q = 1) (hb : d93635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92816, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92816, d93635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92843 q = 1) (hb : d93656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92843, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92843, d93656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11477 (p : Pattern) (ha : d92844 p = 1) (hb : d93657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6957 q = 1) (hb : d81745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11470 q ha hb
    | true =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6958 q = 1) (hb : d81746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d81746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92818 q = 1) (hb : d93637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92818, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92818, d93637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92819 q = 1) (hb : d93638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92819, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92819, d93638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92820 q = 1) (hb : d93639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92820, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92820, d93639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92844 q = 1) (hb : d93657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92844, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92844, d93657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11478 (p : Pattern) (ha : d92853 p = 1) (hb : d93663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92799 q = 1) (hb : d93623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92799, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11466 q ha hb
    | true =>
      simp only [d92799, d93623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d92800 q = 1) (hb : d93624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92800, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92800, d93624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92801 q = 1) (hb : d93625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92801, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92801, d93625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92802 q = 1) (hb : d93626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92802, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92802, d93626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92806 q = 1) (hb : d93630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92806, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11467 q ha hb
    | true =>
      simp only [d92806, d93630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d92807 q = 1) (hb : d93631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92807, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92807, d93631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92808 q = 1) (hb : d93632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92808, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92808, d93632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92822 q = 1) (hb : d93641 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92822, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11469 q ha hb
    | true =>
      simp only [d92822, d93641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11471 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92823 q = 1) (hb : d93642 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92823, d93642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8809 q = 1) (hb : d92828 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8809, d92828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11465 q ha hb
    | true =>
      simp only [d8809, d92828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8810 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8810, d92829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8810, d92829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92830 q = 1) (hb : d93643 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92830, d93643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92831 q = 1) (hb : d93644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92831, d93644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92832 q = 1) (hb : d93645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92832, d93645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92835 q = 1) (hb : d93648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92835, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11474 q ha hb
    | true =>
      simp only [d92835, d93648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q hb ha
  have h17 (q : Pattern) (ha : d92836 q = 1) (hb : d93649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92836, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92836, d93649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92837 q = 1) (hb : d93650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92837, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92837, d93650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92838 q = 1) (hb : d93651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92838, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92838, d93651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92840 q = 1) (hb : d93653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92840, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11475 q ha hb
    | true =>
      simp only [d92840, d93653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q hb ha
  have h21 (q : Pattern) (ha : d92841 q = 1) (hb : d93654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92841, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92841, d93654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92842 q = 1) (hb : d93655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92842, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92842, d93655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92845 q = 1) (hb : d93658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92845, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11476 q ha hb
    | true =>
      simp only [d92845, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11477 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92788 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92846 q = 1) (hb : d93659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92846, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8831 q = 1) (hb : d92848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d92848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11473 q ha hb
    | true =>
      simp only [d8831, d92848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8832 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d92849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8832, d92849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d92850 q = 1) (hb : d93660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92850, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92851 q = 1) (hb : d93661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92851, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92851, d93661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92852 q = 1) (hb : d93662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92852, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92852, d93662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92853 q = 1) (hb : d93663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92853, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92853, d93663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro11479 (p : Pattern) (ha : d92860 p = 1) (hb : d93670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92855 q = 1) (hb : d93665 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92855, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11471 q ha hb
    | true =>
      simp only [d92855, d93665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d92856 q = 1) (hb : d93666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92856, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92856, d93666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92857 q = 1) (hb : d93667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92857, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92857, d93667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92858 q = 1) (hb : d93668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92858, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92858, d93668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92859 q = 1) (hb : d93669 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92859, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92859, d93669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d92860 q = 1) (hb : d93670 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92860, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92860, d93670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro11480 (p : Pattern) (ha : d92867 p = 1) (hb : d93677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92845 q = 1) (hb : d93658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92845, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11476 q ha hb
    | true =>
      simp only [d92845, d93658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11477 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92788 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92846 q = 1) (hb : d93659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92846, d93659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8831 q = 1) (hb : d92848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8831, d92848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11473 q ha hb
    | true =>
      simp only [d8831, d92848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8832 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8832, d92849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8832, d92849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92850 q = 1) (hb : d93660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92850, d93660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92865 q = 1) (hb : d93675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92865, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92865, d93675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92866 q = 1) (hb : d93676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92866, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92866, d93676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92867 q = 1) (hb : d93677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92867, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92867, d93677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11481 (p : Pattern) (ha : d8882 p = 1) (hb : d92888 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d7000 q = 1) (hb : d81788 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1412 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro168 q ha hb
  have h6 (q : Pattern) (ha : d1413 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1414 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1420 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1420, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8881 q = 1) (hb : d92887 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8881, d92887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8881, d92887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8882 q = 1) (hb : d92888 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8882, d92888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8882, d92888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11482 (p : Pattern) (ha : d8888 p = 1) (hb : d92900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d92889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d92889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11481 q ha hb
    | true =>
      simp only [d8883, d92889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d92890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d92890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d92890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8885 q = 1) (hb : d92897 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8885, d92897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8885, d92897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8886 q = 1) (hb : d92898 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8886, d92898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8886, d92898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8887 q = 1) (hb : d92899 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8887, d92899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8887, d92899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8888 q = 1) (hb : d92900 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8888, d92900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8888, d92900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11483 (p : Pattern) (ha : d8858 p = 1) (hb : d92875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d52885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro179 q ha hb
    | true =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d52886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d52887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8856 q = 1) (hb : d92873 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8856, d92873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8856, d92873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h6 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7000 q = 1) (hb : d81788 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8857 q = 1) (hb : d92874 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8857, d92874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8857, d92874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8858 q = 1) (hb : d92875 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8858, d92875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8858, d92875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11484 (p : Pattern) (ha : d92881 p = 1) (hb : d93686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8859 q = 1) (hb : d92876 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8859, d92876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11483 q ha hb
    | true =>
      simp only [d8859, d92876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8860 q = 1) (hb : d92877 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8860, d92877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8860, d92877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81792 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92878 q = 1) (hb : d93683 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92878, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92878, d93683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92879 q = 1) (hb : d93684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92879, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92879, d93684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92880 q = 1) (hb : d93685 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92880, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92880, d93685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92881 q = 1) (hb : d93686 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92881, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92881, d93686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11485 (p : Pattern) (ha : d7002 p = 1) (hb : d81790 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d7000 q = 1) (hb : d81788 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d81788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6356 q = 1) (hb : d76096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d76096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
    | true =>
      simp only [d6356, d76096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10887 q ha hb
  have h6 (q : Pattern) (ha : d6357 q = 1) (hb : d76097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d76097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d76097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6358 q = 1) (hb : d76098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d76098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d76098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6359 q = 1) (hb : d76099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d76099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6359, d76099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7001 q = 1) (hb : d81789 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7001, d81789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7001, d81789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7002 q = 1) (hb : d81790 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7002, d81790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7002, d81790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11486 (p : Pattern) (ha : d92885 p = 1) (hb : d93690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7003 q = 1) (hb : d81791 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d81791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11485 q ha hb
    | true =>
      simp only [d7003, d81791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7004 q = 1) (hb : d81792 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d81792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7004, d81792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92882 q = 1) (hb : d93687 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92882, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92882, d93687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92883 q = 1) (hb : d93688 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92883, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92883, d93688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92884 q = 1) (hb : d93689 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92884, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92884, d93689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92885 q = 1) (hb : d93690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92885, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92885, d93690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro11487 (p : Pattern) (ha : d92906 p = 1) (hb : d93696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92886 q = 1) (hb : d93691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92886, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11484 q ha hb
    | true =>
      simp only [d92886, d93691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11486 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92896 q = 1) (hb : d93692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92896, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92896, d93692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8889 q = 1) (hb : d92901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8889, d92901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11482 q ha hb
    | true =>
      simp only [d8889, d92901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8890 q = 1) (hb : d92902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8890, d92902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8890, d92902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92903 q = 1) (hb : d93693 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92903, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92903, d93693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92904 q = 1) (hb : d93694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92904, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92904, d93694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92905 q = 1) (hb : d93695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92905, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92905, d93695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92906 q = 1) (hb : d93696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92906, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92906, d93696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11488 (p : Pattern) (ha : d92912 p = 1) (hb : d93702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92785 q = 1) (hb : d93610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92785, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92785, d93610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11462 q ha hb
  have h2 (q : Pattern) (ha : d92786 q = 1) (hb : d93611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92786, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92786, d93611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92794 q = 1) (hb : d93618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92794, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11462 q ha hb
    | true =>
      simp only [d92794, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11464 q ha hb
  have h4 (q : Pattern) (ha : d92795 q = 1) (hb : d93619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92795, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92795, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92796 q = 1) (hb : d93620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92796, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92796, d93620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92854 q = 1) (hb : d93664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92854, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11472 q ha hb
    | true =>
      simp only [d92854, d93664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11478 q ha hb
  have h7 (q : Pattern) (ha : d92861 q = 1) (hb : d93671 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92861, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11479 q ha hb
    | true =>
      simp only [d92861, d93671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q hb ha
  have h8 (q : Pattern) (ha : d92862 q = 1) (hb : d93672 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92862, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92862, d93672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92863 q = 1) (hb : d93673 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92863, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92863, d93673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92864 q = 1) (hb : d93674 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92864, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92864, d93674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92868 q = 1) (hb : d93678 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92868, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92868, d93678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11480 q ha hb
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
  have h13 (q : Pattern) (ha : d92869 q = 1) (hb : d93679 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92869, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92869, d93679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92870 q = 1) (hb : d93680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92870, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92870, d93680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92871 q = 1) (hb : d93681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92871, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92871, d93681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92872 q = 1) (hb : d93682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92872, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92872, d93682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92907 q = 1) (hb : d93697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92907, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92907, d93697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11487 q ha hb
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
  have h19 (q : Pattern) (ha : d92908 q = 1) (hb : d93698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92908, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92908, d93698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92909 q = 1) (hb : d93699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92909, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92909, d93699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92910 q = 1) (hb : d93700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92910, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92910, d93700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92911 q = 1) (hb : d93701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92911, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92911, d93701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92912 q = 1) (hb : d93702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92912, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92912, d93702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11489 (p : Pattern) (ha : d92918 p = 1) (hb : d93708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92913 q = 1) (hb : d93703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92913, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92913, d93703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11488 q ha hb
  have h2 (q : Pattern) (ha : d92914 q = 1) (hb : d93704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92914, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92914, d93704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92915 q = 1) (hb : d93705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92915, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92915, d93705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92916 q = 1) (hb : d93706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92916, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92916, d93706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92917 q = 1) (hb : d93707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92917, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92917, d93707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92918 q = 1) (hb : d93708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92918, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92918, d93708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11490 (p : Pattern) (ha : d8911 p = 1) (hb : d92923 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d7034 q = 1) (hb : d81822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1603 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro213 q ha hb
  have h6 (q : Pattern) (ha : d1604 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1605 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1607 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1607, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8910 q = 1) (hb : d92922 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8910, d92922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8910, d92922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8911 q = 1) (hb : d92923 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8911, d92923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8911, d92923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11491 (p : Pattern) (ha : d8976 p = 1) (hb : d92929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d92926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8974 q = 1) (hb : d92927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8975 q = 1) (hb : d92928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d92928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8975, d92928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8976 q = 1) (hb : d92929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, d92929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, d92929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11492 (p : Pattern) (ha : d92935 p = 1) (hb : d93717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92930 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11491 q hb ha
    | true =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d92931 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92931, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92931, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92932 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92932, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92932, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92933 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92933, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92933, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92934 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92934, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92934, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92935 q = 1) (hb : d93717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92935, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92935, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11493 (p : Pattern) (ha : d8998 p = 1) (hb : d92938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d92926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8974 q = 1) (hb : d92927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8975 q = 1) (hb : d92928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d92928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8975, d92928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8998 q = 1) (hb : d92938 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8998, d92938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8998, d92938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro11494 (p : Pattern) (ha : d92944 p = 1) (hb : d93725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92930 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11491 q hb ha
    | true =>
      simp only [d92930, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d92931 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92931, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92931, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92932 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92932, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92932, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92933 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92933, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92933, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92934 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92934, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92934, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92939 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11493 q hb ha
    | true =>
      simp only [d92939, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h7 (q : Pattern) (ha : d92940 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92940, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92940, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92941 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92941, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92941, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92942 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92942, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92942, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92943 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92943, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92943, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92944 q = 1) (hb : d93725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92944, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92944, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11495 (p : Pattern) (ha : d8976 p = 1) (hb : d92978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8973 q = 1) (hb : d92975 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8974 q = 1) (hb : d92976 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d92976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8974, d92976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8975 q = 1) (hb : d92977 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8975, d92977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8975, d92977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8976 q = 1) (hb : d92978 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8976, d92978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8976, d92978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11496 (p : Pattern) (ha : d92949 p = 1) (hb : d93730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d92926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8974 q = 1) (hb : d92927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8974, d92927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92948 q = 1) (hb : d93729 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92948, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92948, d93729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92949 q = 1) (hb : d93730 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92949, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92949, d93730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11497 (p : Pattern) (ha : d92956 p = 1) (hb : d93737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8912 q = 1) (hb : d92924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11490 q ha hb
    | true =>
      simp only [d8912, d92924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8913 q = 1) (hb : d92925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8913, d92925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8973 q = 1) (hb : d92926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8973, d92926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92954 q = 1) (hb : d93735 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92954, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92954, d93735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92955 q = 1) (hb : d93736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92955, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92955, d93736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92956 q = 1) (hb : d93737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92956, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92956, d93737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11498 (p : Pattern) (ha : d8950 p = 1) (hb : d92962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d53112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro231 q ha hb
    | true =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d53113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d53114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8948 q = 1) (hb : d92960 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, d92960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8948, d92960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h6 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7034 q = 1) (hb : d81822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7034, d81822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8949 q = 1) (hb : d92961 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8949, d92961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8949, d92961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8950 q = 1) (hb : d92962 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8950, d92962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8950, d92962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro11499 (p : Pattern) (ha : d92968 p = 1) (hb : d93744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8951 q = 1) (hb : d92963 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8951, d92963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11498 q ha hb
    | true =>
      simp only [d8951, d92963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8952 q = 1) (hb : d92964 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8952, d92964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8952, d92964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81826 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92965 q = 1) (hb : d93741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92965, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92965, d93741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92966 q = 1) (hb : d93742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92966, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92966, d93742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92967 q = 1) (hb : d93743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92967, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92967, d93743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92968 q = 1) (hb : d93744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92968, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92968, d93744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
