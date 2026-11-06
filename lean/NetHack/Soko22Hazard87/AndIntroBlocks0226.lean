import NetHack.Soko22Hazard87.AndIntroBlocks0225
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro56500 (p : Pattern) (ha : d24522 p = 1) (hb : d209101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24360 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d208996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56494 q ha hb
    | true =>
      simp only [d24360, d208996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56495 q ha hb
  have h2 (q : Pattern) (ha : d24361 q = 1) (hb : d208997 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d208997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24361, d208997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24362 q = 1) (hb : d208998 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d208998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24362, d208998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24363 q = 1) (hb : d208999 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d208999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24363, d208999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24364 q = 1) (hb : d209000 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d209000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d209000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24517 q = 1) (hb : d209096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24517, d209096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56495 q ha hb
    | true =>
      simp only [d24517, d209096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24518 q = 1) (hb : d209097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24518, d209097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24518, d209097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24519 q = 1) (hb : d209098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24519, d209098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24519, d209098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24520 q = 1) (hb : d209099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24520, d209099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24520, d209099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24521 q = 1) (hb : d209100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24521, d209100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24521, d209100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24522 q = 1) (hb : d209101 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24522, d209101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24522, d209101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56501 (p : Pattern) (ha : d24528 p = 1) (hb : d209107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24517 q = 1) (hb : d209096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24517, d209096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56495 q ha hb
    | true =>
      simp only [d24517, d209096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24518 q = 1) (hb : d209097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24518, d209097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24518, d209097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24519 q = 1) (hb : d209098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24519, d209098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24519, d209098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24520 q = 1) (hb : d209099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24520, d209099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24520, d209099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24521 q = 1) (hb : d209100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24521, d209100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24521, d209100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24523 q = 1) (hb : d209102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24523, d209102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56498 q ha hb
    | true =>
      simp only [d24523, d209102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24524 q = 1) (hb : d209103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24524, d209103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24524, d209103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24525 q = 1) (hb : d209104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24525, d209104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24525, d209104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24526 q = 1) (hb : d209105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24526, d209105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24526, d209105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24527 q = 1) (hb : d209106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24527, d209106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24527, d209106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24528 q = 1) (hb : d209107 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24528, d209107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24528, d209107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56502 (p : Pattern) (ha : d24537 p = 1) (hb : d209116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24523 q = 1) (hb : d209102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24523, d209102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56498 q ha hb
    | true =>
      simp only [d24523, d209102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24524 q = 1) (hb : d209103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24524, d209103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24524, d209103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24525 q = 1) (hb : d209104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24525, d209104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24525, d209104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24526 q = 1) (hb : d209105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24526, d209105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24526, d209105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24527 q = 1) (hb : d209106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24527, d209106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24527, d209106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24537 q = 1) (hb : d209116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24537, d209116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24537, d209116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56503 (p : Pattern) (ha : d24568 p = 1) (hb : d209147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24552 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
  have h2 (q : Pattern) (ha : d24319 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
    | true =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24553 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24320 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24554 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24555 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24558 q = 1) (hb : d209137 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
  have h8 (q : Pattern) (ha : d24327 q = 1) (hb : d208963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
    | true =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24559 q = 1) (hb : d209138 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24328 q = 1) (hb : d208964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24560 q = 1) (hb : d209139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24561 q = 1) (hb : d209140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24562 q = 1) (hb : d209141 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24562, d209141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24562, d209141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24567 q = 1) (hb : d209146 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24567, d209146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24567, d209146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24568 q = 1) (hb : d209147 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24568, d209147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24568, d209147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56504 (p : Pattern) (ha : d24573 p = 1) (hb : d209152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24558 q = 1) (hb : d209137 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
  have h2 (q : Pattern) (ha : d24327 q = 1) (hb : d208963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
    | true =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24559 q = 1) (hb : d209138 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24328 q = 1) (hb : d208964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24560 q = 1) (hb : d209139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24561 q = 1) (hb : d209140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24567 q = 1) (hb : d209146 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24567, d209146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24567, d209146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1883 q = 1) (hb : d53209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
  have h9 (q : Pattern) (ha : d1597 q = 1) (hb : d53038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro212 q ha hb
    | true =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1884 q = 1) (hb : d53210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1598 q = 1) (hb : d53039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1885 q = 1) (hb : d53211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1886 q = 1) (hb : d53212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1887 q = 1) (hb : d53213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24573 q = 1) (hb : d209152 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24573, d209152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24573, d209152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56505 (p : Pattern) (ha : d24592 p = 1) (hb : d209171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24574 q = 1) (hb : d209153 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56503 q ha hb
    | true =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56504 q ha hb
  have h2 (q : Pattern) (ha : d24575 q = 1) (hb : d209154 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24576 q = 1) (hb : d209155 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24582 q = 1) (hb : d209161 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24582, d209161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24582, d209161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24591 q = 1) (hb : d209170 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24591, d209170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24591, d209170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24592 q = 1) (hb : d209171 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24592, d209171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24592, d209171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56506 (p : Pattern) (ha : d24667 p = 1) (hb : d209182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24593 q = 1) (hb : d209172 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24593, d209172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56505 q ha hb
    | true =>
      simp only [d24593, d209172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24594 q = 1) (hb : d209173 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24594, d209173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24594, d209173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24664 q = 1) (hb : d209179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24664, d209179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24664, d209179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24665 q = 1) (hb : d209180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24665, d209180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24665, d209180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24666 q = 1) (hb : d209181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24666, d209181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24666, d209181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24667 q = 1) (hb : d209182 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24667, d209182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24667, d209182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56507 (p : Pattern) (ha : d24673 p = 1) (hb : d209210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24668 q = 1) (hb : d209205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24668, d209205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56506 q ha hb
    | true =>
      simp only [d24668, d209205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24669 q = 1) (hb : d209206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24669, d209206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24669, d209206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24670 q = 1) (hb : d209207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24670, d209207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24670, d209207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24671 q = 1) (hb : d209208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24671, d209208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24671, d209208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24672 q = 1) (hb : d209209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24672, d209209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24672, d209209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24673 q = 1) (hb : d209210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24673, d209210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24673, d209210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56508 (p : Pattern) (ha : d24380 p = 1) (hb : d209016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208982 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56492 q ha hb
    | true =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208983 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208988 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24353 q = 1) (hb : d208989 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24353, d208989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24353, d208989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24379 q = 1) (hb : d209015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24379, d209015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24379, d209015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24380 q = 1) (hb : d209016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24380, d209016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24380, d209016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56509 (p : Pattern) (ha : d24382 p = 1) (hb : d209018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208992 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24357 q = 1) (hb : d208993 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24357, d208993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24357, d208993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24381 q = 1) (hb : d209017 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24381, d209017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24381, d209017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24382 q = 1) (hb : d209018 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24382, d209018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24382, d209018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56510 (p : Pattern) (ha : d24389 p = 1) (hb : d209025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208982 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56492 q ha hb
    | true =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208983 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208988 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24387 q = 1) (hb : d209023 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24387, d209023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24387, d209023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24388 q = 1) (hb : d209024 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24388, d209024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24388, d209024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24389 q = 1) (hb : d209025 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24389, d209025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24389, d209025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56511 (p : Pattern) (ha : d24392 p = 1) (hb : d209028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208992 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24390 q = 1) (hb : d209026 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24390, d209026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24390, d209026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24391 q = 1) (hb : d209027 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24391, d209027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24391, d209027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24392 q = 1) (hb : d209028 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24392, d209028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24392, d209028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56512 (p : Pattern) (ha : d24398 p = 1) (hb : d209034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1660 q = 1) (hb : d53101 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1660, d53101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1660, d53101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24396 q = 1) (hb : d209032 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24396, d209032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24396, d209032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24397 q = 1) (hb : d209033 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24397, d209033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24397, d209033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h7 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h8 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1530 q = 1) (hb : d52971 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1530, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24307 q = 1) (hb : d208943 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24307, d208943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24307, d208943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24308 q = 1) (hb : d208944 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24308, d208944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24308, d208944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24398 q = 1) (hb : d209034 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24398, d209034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24398, d209034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro56513 (p : Pattern) (ha : d24404 p = 1) (hb : d209040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24399 q = 1) (hb : d209035 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24399, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56512 q ha hb
    | true =>
      simp only [d24399, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24400 q = 1) (hb : d209036 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24400, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24400, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24401 q = 1) (hb : d209037 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24401, d209037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24401, d209037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24402 q = 1) (hb : d209038 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24402, d209038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24402, d209038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24312 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24312, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56486 q ha hb
    | true =>
      simp only [d24312, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24313 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24313, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24313, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24314 q = 1) (hb : d208950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24314, d208950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24314, d208950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24315 q = 1) (hb : d208951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24315, d208951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24315, d208951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24403 q = 1) (hb : d209039 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24403, d209039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24403, d209039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24319 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
    | true =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24320 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24321 q = 1) (hb : d208957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24321, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24321, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24322 q = 1) (hb : d208958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24322, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24322, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d24323 q = 1) (hb : d208959 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24323, d208959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24323, d208959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24404 q = 1) (hb : d209040 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24404, d209040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24404, d209040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56514 (p : Pattern) (ha : d24410 p = 1) (hb : d209046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24405 q = 1) (hb : d209041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24405, d209041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56513 q ha hb
    | true =>
      simp only [d24405, d209041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56489 q ha hb
  have h2 (q : Pattern) (ha : d24406 q = 1) (hb : d209042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24406, d209042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24406, d209042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24407 q = 1) (hb : d209043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24407, d209043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24407, d209043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24335 q = 1) (hb : d208971 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24335, d208971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56489 q ha hb
    | true =>
      simp only [d24335, d208971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56490 q ha hb
  have h5 (q : Pattern) (ha : d24336 q = 1) (hb : d208972 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24336, d208972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24336, d208972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24337 q = 1) (hb : d208973 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24337, d208973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24337, d208973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24408 q = 1) (hb : d209044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24408, d209044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24408, d209044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24339 q = 1) (hb : d208975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24339, d208975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56490 q ha hb
    | true =>
      simp only [d24339, d208975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56491 q ha hb
  have h9 (q : Pattern) (ha : d24340 q = 1) (hb : d208976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24340, d208976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24340, d208976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24341 q = 1) (hb : d208977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24341, d208977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24341, d208977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24342 q = 1) (hb : d208978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24342, d208978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24342, d208978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24409 q = 1) (hb : d209045 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24409, d209045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24409, d209045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24410 q = 1) (hb : d209046 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24410, d209046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24410, d209046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56515 (p : Pattern) (ha : d24416 p = 1) (hb : d209052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24411 q = 1) (hb : d209047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24411, d209047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56514 q ha hb
    | true =>
      simp only [d24411, d209047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24412 q = 1) (hb : d209048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24412, d209048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24412, d209048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24346 q = 1) (hb : d208982 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56492 q ha hb
    | true =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24347 q = 1) (hb : d208983 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24413 q = 1) (hb : d209049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24413, d209049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24413, d209049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24414 q = 1) (hb : d209050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24414, d209050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24414, d209050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24415 q = 1) (hb : d209051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24415, d209051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24415, d209051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24416 q = 1) (hb : d209052 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24416, d209052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24416, d209052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56516 (p : Pattern) (ha : d24473 p = 1) (hb : d209055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24319 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
    | true =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24320 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24321 q = 1) (hb : d208957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24321, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24321, d208957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24322 q = 1) (hb : d208958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24322, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24322, d208958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24327 q = 1) (hb : d208963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
    | true =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24328 q = 1) (hb : d208964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24329 q = 1) (hb : d208965 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24329, d208965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24329, d208965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24330 q = 1) (hb : d208966 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24330, d208966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24330, d208966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24331 q = 1) (hb : d208967 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24331, d208967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24331, d208967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5630 q = 1) (hb : d74356 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9291 q ha hb
    | true =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5631 q = 1) (hb : d74357 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5632 q = 1) (hb : d74358 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d74358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5632, d74358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5633 q = 1) (hb : d74359 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d74359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5633, d74359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5634 q = 1) (hb : d74360 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, d74360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5634, d74360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24473 q = 1) (hb : d209055 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24473, d209055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24473, d209055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56517 (p : Pattern) (ha : d24479 p = 1) (hb : d209061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24335 q = 1) (hb : d208971 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24335, d208971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56489 q ha hb
    | true =>
      simp only [d24335, d208971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56490 q ha hb
  have h2 (q : Pattern) (ha : d24336 q = 1) (hb : d208972 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24336, d208972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24336, d208972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24337 q = 1) (hb : d208973 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24337, d208973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24337, d208973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24339 q = 1) (hb : d208975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24339, d208975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56490 q ha hb
    | true =>
      simp only [d24339, d208975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56491 q ha hb
  have h5 (q : Pattern) (ha : d24340 q = 1) (hb : d208976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24340, d208976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24340, d208976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24341 q = 1) (hb : d208977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24341, d208977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24341, d208977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24342 q = 1) (hb : d208978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24342, d208978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24342, d208978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24474 q = 1) (hb : d209056 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24474, d209056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56516 q ha hb
    | true =>
      simp only [d24474, d209056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9293 q ha hb
  have h9 (q : Pattern) (ha : d24475 q = 1) (hb : d209057 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24475, d209057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24475, d209057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24476 q = 1) (hb : d209058 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24476, d209058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24476, d209058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24477 q = 1) (hb : d209059 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24477, d209059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24477, d209059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24478 q = 1) (hb : d209060 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24478, d209060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24478, d209060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24479 q = 1) (hb : d209061 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24479, d209061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24479, d209061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56518 (p : Pattern) (ha : d24485 p = 1) (hb : d209067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24480 q = 1) (hb : d209062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24480, d209062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56517 q ha hb
    | true =>
      simp only [d24480, d209062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24481 q = 1) (hb : d209063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24481, d209063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24481, d209063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24482 q = 1) (hb : d209064 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24482, d209064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24482, d209064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24483 q = 1) (hb : d209065 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24483, d209065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24483, d209065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24484 q = 1) (hb : d209066 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24484, d209066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24484, d209066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24485 q = 1) (hb : d209067 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24485, d209067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24485, d209067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56519 (p : Pattern) (ha : d209073 p = 1) (hb : d211286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24383 q = 1) (hb : d209019 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24383, d209019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56508 q ha hb
    | true =>
      simp only [d24383, d209019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56509 q ha hb
  have h2 (q : Pattern) (ha : d24384 q = 1) (hb : d209020 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24384, d209020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24384, d209020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24385 q = 1) (hb : d209021 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24385, d209021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24385, d209021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24386 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24386, d209022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24386, d209022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24393 q = 1) (hb : d209029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24393, d209029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56510 q ha hb
    | true =>
      simp only [d24393, d209029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56511 q ha hb
  have h6 (q : Pattern) (ha : d24394 q = 1) (hb : d209030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24394, d209030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24394, d209030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24395 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24395, d209031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24395, d209031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24417 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24417, d209053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56515 q ha hb
    | true =>
      simp only [d24417, d209053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56494 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209054 q = 1) (hb : d211282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d209054, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d24486 q = 1) (hb : d209068 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24486, d209068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56518 q ha hb
    | true =>
      simp only [d24486, d209068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24487 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24487, d209069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24487, d209069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d209070 q = 1) (hb : d211283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209070, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d209071 q = 1) (hb : d211284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d209071, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209072 q = 1) (hb : d211285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209072, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209073 q = 1) (hb : d211286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209073, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209073, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro56520 (p : Pattern) (ha : d24492 p = 1) (hb : d209074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208982 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56492 q ha hb
    | true =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208983 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208988 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24353 q = 1) (hb : d208989 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24353, d208989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24353, d208989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24379 q = 1) (hb : d209015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24379, d209015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24379, d209015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24492 q = 1) (hb : d209074 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24492, d209074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24492, d209074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56521 (p : Pattern) (ha : d24493 p = 1) (hb : d209075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208992 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24357 q = 1) (hb : d208993 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24357, d208993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24357, d208993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24381 q = 1) (hb : d209017 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24381, d209017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24381, d209017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24493 q = 1) (hb : d209075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24493, d209075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24493, d209075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56522 (p : Pattern) (ha : d24498 p = 1) (hb : d209080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24346 q = 1) (hb : d208982 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56492 q ha hb
    | true =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24347 q = 1) (hb : d208983 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24352 q = 1) (hb : d208988 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24352, d208988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24387 q = 1) (hb : d209023 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24387, d209023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24387, d209023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24388 q = 1) (hb : d209024 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24388, d209024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24388, d209024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24498 q = 1) (hb : d209080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24498, d209080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24498, d209080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56523 (p : Pattern) (ha : d24499 p = 1) (hb : d209081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24350 q = 1) (hb : d208986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56493 q ha hb
    | true =>
      simp only [d24350, d208986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24351 q = 1) (hb : d208987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24351, d208987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24356 q = 1) (hb : d208992 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24356, d208992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24390 q = 1) (hb : d209026 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24390, d209026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24390, d209026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24391 q = 1) (hb : d209027 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24391, d209027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24391, d209027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24499 q = 1) (hb : d209081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24499, d209081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24499, d209081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56524 (p : Pattern) (ha : d24503 p = 1) (hb : d209085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24411 q = 1) (hb : d209047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24411, d209047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56514 q ha hb
    | true =>
      simp only [d24411, d209047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24412 q = 1) (hb : d209048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24412, d209048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24412, d209048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24346 q = 1) (hb : d208982 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56492 q ha hb
    | true =>
      simp only [d24346, d208982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24347 q = 1) (hb : d208983 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24347, d208983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24413 q = 1) (hb : d209049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24413, d209049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24413, d209049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24414 q = 1) (hb : d209050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24414, d209050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24414, d209050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24415 q = 1) (hb : d209051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24415, d209051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24415, d209051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24503 q = 1) (hb : d209085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24503, d209085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24503, d209085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56525 (p : Pattern) (ha : d24509 p = 1) (hb : d209088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24480 q = 1) (hb : d209062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24480, d209062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56517 q ha hb
    | true =>
      simp only [d24480, d209062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24481 q = 1) (hb : d209063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24481, d209063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24481, d209063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24482 q = 1) (hb : d209064 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24482, d209064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24482, d209064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24483 q = 1) (hb : d209065 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24483, d209065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24483, d209065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24484 q = 1) (hb : d209066 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24484, d209066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24484, d209066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24509 q = 1) (hb : d209088 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24509, d209088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24509, d209088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56526 (p : Pattern) (ha : d209094 p = 1) (hb : d211291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24383 q = 1) (hb : d209019 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24383, d209019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56508 q ha hb
    | true =>
      simp only [d24383, d209019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56509 q ha hb
  have h2 (q : Pattern) (ha : d24384 q = 1) (hb : d209020 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24384, d209020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24384, d209020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24385 q = 1) (hb : d209021 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24385, d209021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24385, d209021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24386 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24386, d209022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24386, d209022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24393 q = 1) (hb : d209029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24393, d209029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56510 q ha hb
    | true =>
      simp only [d24393, d209029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56511 q ha hb
  have h6 (q : Pattern) (ha : d24394 q = 1) (hb : d209030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24394, d209030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24394, d209030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24395 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24395, d209031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24395, d209031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24417 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24417, d209053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56515 q ha hb
    | true =>
      simp only [d24417, d209053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56494 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209054 q = 1) (hb : d211282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d209054, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d24486 q = 1) (hb : d209068 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24486, d209068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56518 q ha hb
    | true =>
      simp only [d24486, d209068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24487 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24487, d209069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24487, d209069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d209070 q = 1) (hb : d211283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209070, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d209071 q = 1) (hb : d211284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d209071, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209072 q = 1) (hb : d211285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209072, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24494 q = 1) (hb : d209076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24494, d209076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56520 q ha hb
    | true =>
      simp only [d24494, d209076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56521 q ha hb
  have h17 (q : Pattern) (ha : d24495 q = 1) (hb : d209077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24495, d209077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24495, d209077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24496 q = 1) (hb : d209078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24496, d209078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d24496, d209078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d24497 q = 1) (hb : d209079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24497, d209079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24497, d209079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d24500 q = 1) (hb : d209082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24500, d209082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56522 q ha hb
    | true =>
      simp only [d24500, d209082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56523 q ha hb
  have h21 (q : Pattern) (ha : d24501 q = 1) (hb : d209083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24501, d209083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24501, d209083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d24502 q = 1) (hb : d209084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24502, d209084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d24502, d209084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d24504 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24504, d209086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56524 q ha hb
    | true =>
      simp only [d24504, d209086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56497 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d209087 q = 1) (hb : d211287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d209087, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d24510 q = 1) (hb : d209089 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24510, d209089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56525 q ha hb
    | true =>
      simp only [d24510, d209089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d24511 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24511, d209090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d24511, d209090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d209091 q = 1) (hb : d211288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d209091, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d209092 q = 1) (hb : d211289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209092, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d209092, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d209093 q = 1) (hb : d211290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209093, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d209093, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d209094 q = 1) (hb : d211291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209094, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209094, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro56527 (p : Pattern) (ha : d209114 p = 1) (hb : d211298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24504 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24504, d209086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56524 q ha hb
    | true =>
      simp only [d24504, d209086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56497 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209087 q = 1) (hb : d211287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209087, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d24510 q = 1) (hb : d209089 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24510, d209089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56525 q ha hb
    | true =>
      simp only [d24510, d209089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24511 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24511, d209090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24511, d209090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d209091 q = 1) (hb : d211288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209091, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209112 q = 1) (hb : d211296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209112, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209112, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209113 q = 1) (hb : d211297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209113, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209113, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209114 q = 1) (hb : d211298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209114, d211298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209114, d211298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56528 (p : Pattern) (ha : d24557 p = 1) (hb : d209136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24543 q = 1) (hb : d209122 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24543, d209122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24543, d209122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56512 q ha hb
  have h2 (q : Pattern) (ha : d24399 q = 1) (hb : d209035 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24399, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56512 q ha hb
    | true =>
      simp only [d24399, d209035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24544 q = 1) (hb : d209123 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24544, d209123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24544, d209123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24400 q = 1) (hb : d209036 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24400, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24400, d209036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24545 q = 1) (hb : d209124 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24545, d209124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24545, d209124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24546 q = 1) (hb : d209125 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24546, d209125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24546, d209125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24547 q = 1) (hb : d209126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24547, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24547, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56486 q ha hb
  have h8 (q : Pattern) (ha : d24312 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24312, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56486 q ha hb
    | true =>
      simp only [d24312, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24548 q = 1) (hb : d209127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24548, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24548, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24313 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24313, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24313, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24549 q = 1) (hb : d209128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24549, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24549, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24550 q = 1) (hb : d209129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24550, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24550, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24551 q = 1) (hb : d209130 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24551, d209130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24551, d209130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24552 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
  have h15 (q : Pattern) (ha : d24319 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
    | true =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24553 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24320 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24554 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24555 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24556 q = 1) (hb : d209135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24556, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24556, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24557 q = 1) (hb : d209136 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24557, d209136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24557, d209136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56529 (p : Pattern) (ha : d24563 p = 1) (hb : d209142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24547 q = 1) (hb : d209126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24547, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24547, d209126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56486 q ha hb
  have h2 (q : Pattern) (ha : d24312 q = 1) (hb : d208948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24312, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56486 q ha hb
    | true =>
      simp only [d24312, d208948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24548 q = 1) (hb : d209127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24548, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24548, d209127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24313 q = 1) (hb : d208949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24313, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24313, d208949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24549 q = 1) (hb : d209128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24549, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24549, d209128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24550 q = 1) (hb : d209129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24550, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24550, d209129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24552 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
  have h8 (q : Pattern) (ha : d24319 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
    | true =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24553 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24320 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24554 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24555 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24556 q = 1) (hb : d209135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24556, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24556, d209135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24558 q = 1) (hb : d209137 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
  have h15 (q : Pattern) (ha : d24327 q = 1) (hb : d208963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
    | true =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24559 q = 1) (hb : d209138 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24328 q = 1) (hb : d208964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24560 q = 1) (hb : d209139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24561 q = 1) (hb : d209140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24562 q = 1) (hb : d209141 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24562, d209141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24562, d209141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24563 q = 1) (hb : d209142 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24563, d209142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24563, d209142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56530 (p : Pattern) (ha : d24579 p = 1) (hb : d209158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24564 q = 1) (hb : d209143 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24564, d209143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56528 q ha hb
    | true =>
      simp only [d24564, d209143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56529 q ha hb
  have h2 (q : Pattern) (ha : d24565 q = 1) (hb : d209144 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24565, d209144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24565, d209144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24566 q = 1) (hb : d209145 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24566, d209145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24566, d209145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24569 q = 1) (hb : d209148 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24569, d209148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56529 q ha hb
    | true =>
      simp only [d24569, d209148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56503 q ha hb
  have h5 (q : Pattern) (ha : d24570 q = 1) (hb : d209149 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24570, d209149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24570, d209149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24571 q = 1) (hb : d209150 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24571, d209150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24571, d209150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24572 q = 1) (hb : d209151 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24572, d209151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24572, d209151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24574 q = 1) (hb : d209153 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56503 q ha hb
    | true =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56504 q ha hb
  have h9 (q : Pattern) (ha : d24575 q = 1) (hb : d209154 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24576 q = 1) (hb : d209155 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24577 q = 1) (hb : d209156 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24577, d209156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24577, d209156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24578 q = 1) (hb : d209157 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24578, d209157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24578, d209157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24579 q = 1) (hb : d209158 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24579, d209158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24579, d209158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56531 (p : Pattern) (ha : d24584 p = 1) (hb : d209163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24569 q = 1) (hb : d209148 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24569, d209148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56529 q ha hb
    | true =>
      simp only [d24569, d209148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56503 q ha hb
  have h2 (q : Pattern) (ha : d24570 q = 1) (hb : d209149 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24570, d209149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24570, d209149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24571 q = 1) (hb : d209150 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24571, d209150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24571, d209150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24574 q = 1) (hb : d209153 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56503 q ha hb
    | true =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56504 q ha hb
  have h5 (q : Pattern) (ha : d24575 q = 1) (hb : d209154 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24576 q = 1) (hb : d209155 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24577 q = 1) (hb : d209156 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24577, d209156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24577, d209156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24582 q = 1) (hb : d209161 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24582, d209161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24582, d209161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24583 q = 1) (hb : d209162 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24583, d209162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24583, d209162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24584 q = 1) (hb : d209163 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24584, d209163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24584, d209163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56532 (p : Pattern) (ha : d24590 p = 1) (hb : d209169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24580 q = 1) (hb : d209159 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24580, d209159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56530 q ha hb
    | true =>
      simp only [d24580, d209159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24581 q = 1) (hb : d209160 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24581, d209160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24581, d209160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24585 q = 1) (hb : d209164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24585, d209164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56531 q ha hb
    | true =>
      simp only [d24585, d209164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24586 q = 1) (hb : d209165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24586, d209165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24586, d209165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24587 q = 1) (hb : d209166 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24587, d209166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24587, d209166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24588 q = 1) (hb : d209167 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24588, d209167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24588, d209167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24589 q = 1) (hb : d209168 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24589, d209168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24589, d209168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24590 q = 1) (hb : d209169 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24590, d209169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24590, d209169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56533 (p : Pattern) (ha : d24598 p = 1) (hb : d209177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24585 q = 1) (hb : d209164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24585, d209164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56531 q ha hb
    | true =>
      simp only [d24585, d209164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24586 q = 1) (hb : d209165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24586, d209165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24586, d209165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24593 q = 1) (hb : d209172 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24593, d209172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56505 q ha hb
    | true =>
      simp only [d24593, d209172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24594 q = 1) (hb : d209173 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24594, d209173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24594, d209173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24595 q = 1) (hb : d209174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24595, d209174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24595, d209174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24596 q = 1) (hb : d209175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24596, d209175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24596, d209175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24597 q = 1) (hb : d209176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24597, d209176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24597, d209176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24598 q = 1) (hb : d209177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24598, d209177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24598, d209177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56534 (p : Pattern) (ha : d24644 p = 1) (hb : d209185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24552 q = 1) (hb : d209131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24552, d209131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
  have h2 (q : Pattern) (ha : d24319 q = 1) (hb : d208955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56487 q ha hb
    | true =>
      simp only [d24319, d208955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24553 q = 1) (hb : d209132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24553, d209132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24320 q = 1) (hb : d208956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24320, d208956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24554 q = 1) (hb : d209133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24554, d209133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24555 q = 1) (hb : d209134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24555, d209134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24558 q = 1) (hb : d209137 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24558, d209137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
  have h8 (q : Pattern) (ha : d24327 q = 1) (hb : d208963 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56488 q ha hb
    | true =>
      simp only [d24327, d208963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24559 q = 1) (hb : d209138 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24559, d209138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24328 q = 1) (hb : d208964 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24328, d208964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24560 q = 1) (hb : d209139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24560, d209139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24561 q = 1) (hb : d209140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24561, d209140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24562 q = 1) (hb : d209141 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24562, d209141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24562, d209141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5674 q = 1) (hb : d74400 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d74400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5674, d74400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9291 q ha hb
  have h15 (q : Pattern) (ha : d5630 q = 1) (hb : d74356 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9291 q ha hb
    | true =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5675 q = 1) (hb : d74401 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d74401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5675, d74401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5631 q = 1) (hb : d74357 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5676 q = 1) (hb : d74402 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d74402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5676, d74402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5677 q = 1) (hb : d74403 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d74403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5677, d74403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5678 q = 1) (hb : d74404 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, d74404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5678, d74404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d24644 q = 1) (hb : d209185 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24644, d209185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24644, d209185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56535 (p : Pattern) (ha : d24650 p = 1) (hb : d209191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24569 q = 1) (hb : d209148 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24569, d209148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56529 q ha hb
    | true =>
      simp only [d24569, d209148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56503 q ha hb
  have h2 (q : Pattern) (ha : d24570 q = 1) (hb : d209149 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24570, d209149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24570, d209149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24571 q = 1) (hb : d209150 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24571, d209150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24571, d209150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24574 q = 1) (hb : d209153 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56503 q ha hb
    | true =>
      simp only [d24574, d209153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56504 q ha hb
  have h5 (q : Pattern) (ha : d24575 q = 1) (hb : d209154 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24575, d209154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24576 q = 1) (hb : d209155 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24576, d209155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24577 q = 1) (hb : d209156 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24577, d209156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24577, d209156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24645 q = 1) (hb : d209186 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24645, d209186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56534 q ha hb
    | true =>
      simp only [d24645, d209186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9301 q ha hb
  have h9 (q : Pattern) (ha : d24646 q = 1) (hb : d209187 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24646, d209187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24646, d209187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24647 q = 1) (hb : d209188 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24647, d209188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24647, d209188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24648 q = 1) (hb : d209189 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24648, d209189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24648, d209189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24649 q = 1) (hb : d209190 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24649, d209190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24649, d209190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24650 q = 1) (hb : d209191 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24650, d209191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24650, d209191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56536 (p : Pattern) (ha : d24656 p = 1) (hb : d209197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24651 q = 1) (hb : d209192 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24651, d209192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56535 q ha hb
    | true =>
      simp only [d24651, d209192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24652 q = 1) (hb : d209193 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24652, d209193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24652, d209193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24653 q = 1) (hb : d209194 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24653, d209194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24653, d209194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24654 q = 1) (hb : d209195 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24654, d209195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24654, d209195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24655 q = 1) (hb : d209196 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24655, d209196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24655, d209196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24656 q = 1) (hb : d209197 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24656, d209197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24656, d209197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56537 (p : Pattern) (ha : d209203 p = 1) (hb : d211308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24599 q = 1) (hb : d209178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24599, d209178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56532 q ha hb
    | true =>
      simp only [d24599, d209178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56533 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209184 q = 1) (hb : d211304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209184, d211304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209184, d211304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d24657 q = 1) (hb : d209198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24657, d209198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56536 q ha hb
    | true =>
      simp only [d24657, d209198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24658 q = 1) (hb : d209199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24658, d209199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24658, d209199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d209200 q = 1) (hb : d211305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209200, d211305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209200, d211305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209201 q = 1) (hb : d211306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209201, d211306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209201, d211306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209202 q = 1) (hb : d211307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209202, d211307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209202, d211307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209203 q = 1) (hb : d211308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209203, d211308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209203, d211308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56538 (p : Pattern) (ha : d209216 p = 1) (hb : d211314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24366 q = 1) (hb : d209002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24366, d209002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24366, d209002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56496 q ha hb
  have h2 (q : Pattern) (ha : d24367 q = 1) (hb : d209003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24367, d209003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24367, d209003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24376 q = 1) (hb : d209012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d209012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56496 q ha hb
    | true =>
      simp only [d24376, d209012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56499 q ha hb
  have h4 (q : Pattern) (ha : d24377 q = 1) (hb : d209013 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d209013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24377, d209013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24378 q = 1) (hb : d209014 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d24378, d209014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24378, d209014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209095 q = 1) (hb : d211292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209095, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56519 q ha hb
    | true =>
      simp only [d209095, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56526 q ha hb
  have h7 (q : Pattern) (ha : d24529 q = 1) (hb : d209108 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24529, d209108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56500 q ha hb
    | true =>
      simp only [d24529, d209108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56501 q ha hb
  have h8 (q : Pattern) (ha : d209109 q = 1) (hb : d211293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209109, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209109, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d209110 q = 1) (hb : d211294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209110, d211294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209110, d211294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d209111 q = 1) (hb : d211295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209111, d211295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d209111, d211295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209115 q = 1) (hb : d211299 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209115, d211299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209115, d211299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56527 q ha hb
  have h12 (q : Pattern) (ha : d24538 q = 1) (hb : d209117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24538, d209117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24538, d209117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56502 q ha hb
  have h13 (q : Pattern) (ha : d209118 q = 1) (hb : d211300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209118, d211300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209118, d211300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d209119 q = 1) (hb : d211301 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209119, d211301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209119, d211301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209120 q = 1) (hb : d211302 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209120, d211302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209120, d211302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209121 q = 1) (hb : d211303 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209121, d211303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209121, d211303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209204 q = 1) (hb : d211309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209204, d211309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209204, d211309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56537 q ha hb
  have h18 (q : Pattern) (ha : d24674 q = 1) (hb : d209211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24674, d209211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24674, d209211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56507 q ha hb
  have h19 (q : Pattern) (ha : d209212 q = 1) (hb : d211310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209212, d211310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209212, d211310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d209213 q = 1) (hb : d211311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209213, d211311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209213, d211311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209214 q = 1) (hb : d211312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209214, d211312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d209214, d211312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d209215 q = 1) (hb : d211313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209215, d211313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209215, d211313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209216 q = 1) (hb : d211314 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209216, d211314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209216, d211314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro56539 (p : Pattern) (ha : d209222 p = 1) (hb : d211320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209217 q = 1) (hb : d211315 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209217, d211315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209217, d211315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56538 q ha hb
  have h2 (q : Pattern) (ha : d209218 q = 1) (hb : d211316 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209218, d211316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209218, d211316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209219 q = 1) (hb : d211317 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209219, d211317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209219, d211317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209220 q = 1) (hb : d211318 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209220, d211318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209220, d211318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209221 q = 1) (hb : d211319 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209221, d211319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209221, d211319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209222 q = 1) (hb : d211320 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209222, d211320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209222, d211320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56540 (p : Pattern) (ha : d24692 p = 1) (hb : d209229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2010 q = 1) (hb : d53289 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2011 q = 1) (hb : d53290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2012 q = 1) (hb : d53291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h8 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h9 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2026 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24690 q = 1) (hb : d209227 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24690, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24690, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24691 q = 1) (hb : d209228 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24691, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24691, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24692 q = 1) (hb : d209229 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24692, d209229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24692, d209229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro56541 (p : Pattern) (ha : d24699 p = 1) (hb : d209236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h5 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h6 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2026 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24690 q = 1) (hb : d209227 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24690, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24690, d209227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d24691 q = 1) (hb : d209228 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24691, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24691, d209228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2041 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h11 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h12 (q : Pattern) (ha : d2044 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2045 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24697 q = 1) (hb : d209234 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24697, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24697, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d24698 q = 1) (hb : d209235 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24698, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24698, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d24699 q = 1) (hb : d209236 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24699, d209236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24699, d209236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro56542 (p : Pattern) (ha : d24707 p = 1) (hb : d209244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2041 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h5 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h6 (q : Pattern) (ha : d2044 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2045 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24697 q = 1) (hb : d209234 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24697, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24697, d209234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d24698 q = 1) (hb : d209235 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24698, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24698, d209235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h11 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d2060 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24705 q = 1) (hb : d209242 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24705, d209242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24705, d209242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d24706 q = 1) (hb : d209243 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24706, d209243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d24706, d209243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d24707 q = 1) (hb : d209244 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24707, d209244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24707, d209244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro56543 (p : Pattern) (ha : d24713 p = 1) (hb : d209250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24693 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56540 q ha hb
    | true =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24694 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24695 q = 1) (hb : d209232 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24695, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24695, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24696 q = 1) (hb : d209233 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24696, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24696, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24702 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24703 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24704 q = 1) (hb : d209241 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24704, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24704, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24710 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24711 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d24712 q = 1) (hb : d209249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24712, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24712, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24713 q = 1) (hb : d209250 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24713, d209250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24713, d209250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56544 (p : Pattern) (ha : d24715 p = 1) (hb : d209252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24702 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24703 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24710 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24711 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24712 q = 1) (hb : d209249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24712, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24712, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24714 q = 1) (hb : d209251 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24714, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24714, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24715 q = 1) (hb : d209252 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24715, d209252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24715, d209252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56545 (p : Pattern) (ha : d24719 p = 1) (hb : d209256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24710 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24711 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24714 q = 1) (hb : d209251 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24714, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24714, d209251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2082 q = 1) (hb : d53361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2083 q = 1) (hb : d53362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2084 q = 1) (hb : d53363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24719 q = 1) (hb : d209256 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24719, d209256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24719, d209256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56546 (p : Pattern) (ha : d24726 p = 1) (hb : d209263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24716 q = 1) (hb : d209253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24716, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56543 q ha hb
    | true =>
      simp only [d24716, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56544 q ha hb
  have h2 (q : Pattern) (ha : d24717 q = 1) (hb : d209254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24717, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24717, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24718 q = 1) (hb : d209255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24718, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24718, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24720 q = 1) (hb : d209257 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56544 q ha hb
    | true =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56545 q ha hb
  have h5 (q : Pattern) (ha : d24721 q = 1) (hb : d209258 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24722 q = 1) (hb : d209259 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24723 q = 1) (hb : d209260 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24723, d209260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24723, d209260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24724 q = 1) (hb : d209261 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24724, d209261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24724, d209261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24725 q = 1) (hb : d209262 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24725, d209262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24725, d209262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24726 q = 1) (hb : d209263 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24726, d209263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24726, d209263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56547 (p : Pattern) (ha : d24730 p = 1) (hb : d209267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24720 q = 1) (hb : d209257 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56544 q ha hb
    | true =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56545 q ha hb
  have h2 (q : Pattern) (ha : d24721 q = 1) (hb : d209258 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24722 q = 1) (hb : d209259 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24724 q = 1) (hb : d209261 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24724, d209261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24724, d209261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24729 q = 1) (hb : d209266 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24729, d209266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24729, d209266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24730 q = 1) (hb : d209267 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24730, d209267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24730, d209267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56548 (p : Pattern) (ha : d24736 p = 1) (hb : d209273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24733 q = 1) (hb : d209270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24734 q = 1) (hb : d209271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24735 q = 1) (hb : d209272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24735, d209272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24735, d209272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24736 q = 1) (hb : d209273 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24736, d209273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24736, d209273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56549 (p : Pattern) (ha : d24740 p = 1) (hb : d209277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24737 q = 1) (hb : d209274 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24738 q = 1) (hb : d209275 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24739 q = 1) (hb : d209276 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24739, d209276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24739, d209276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24740 q = 1) (hb : d209277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24740, d209277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24740, d209277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56550 (p : Pattern) (ha : d24746 p = 1) (hb : d209283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24741 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56548 q ha hb
    | true =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56549 q ha hb
  have h2 (q : Pattern) (ha : d24742 q = 1) (hb : d209279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d209279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24742, d209279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24743 q = 1) (hb : d209280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d209280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24743, d209280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24744 q = 1) (hb : d209281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d209281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24744, d209281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24745 q = 1) (hb : d209282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d209282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24745, d209282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24746 q = 1) (hb : d209283 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24746, d209283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24746, d209283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56551 (p : Pattern) (ha : d24749 p = 1) (hb : d209286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24733 q = 1) (hb : d209270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24734 q = 1) (hb : d209271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24735 q = 1) (hb : d209272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24735, d209272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24735, d209272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24749 q = 1) (hb : d209286 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24749, d209286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24749, d209286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56552 (p : Pattern) (ha : d24750 p = 1) (hb : d209287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24737 q = 1) (hb : d209274 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24738 q = 1) (hb : d209275 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24739 q = 1) (hb : d209276 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24739, d209276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24739, d209276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24750 q = 1) (hb : d209287 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24750, d209287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24750, d209287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56553 (p : Pattern) (ha : d24756 p = 1) (hb : d209293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24741 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56548 q ha hb
    | true =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56549 q ha hb
  have h2 (q : Pattern) (ha : d24742 q = 1) (hb : d209279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d209279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24742, d209279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24743 q = 1) (hb : d209280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d209280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24743, d209280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24744 q = 1) (hb : d209281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d209281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24744, d209281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24745 q = 1) (hb : d209282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d209282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24745, d209282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24751 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d209288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56551 q ha hb
    | true =>
      simp only [d24751, d209288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56552 q ha hb
  have h7 (q : Pattern) (ha : d24752 q = 1) (hb : d209289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d209289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24752, d209289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24753 q = 1) (hb : d209290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d209290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24753, d209290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24754 q = 1) (hb : d209291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d209291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d209291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24755 q = 1) (hb : d209292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d209292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d209292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24756 q = 1) (hb : d209293 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24756, d209293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24756, d209293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56554 (p : Pattern) (ha : d24894 p = 1) (hb : d209376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24741 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56548 q ha hb
    | true =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56549 q ha hb
  have h2 (q : Pattern) (ha : d24742 q = 1) (hb : d209279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d209279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24742, d209279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24743 q = 1) (hb : d209280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d209280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24743, d209280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24744 q = 1) (hb : d209281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d209281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24744, d209281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24745 q = 1) (hb : d209282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d209282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24745, d209282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24889 q = 1) (hb : d209371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24889, d209371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56549 q ha hb
    | true =>
      simp only [d24889, d209371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24890 q = 1) (hb : d209372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24890, d209372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24890, d209372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24891 q = 1) (hb : d209373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24891, d209373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24891, d209373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24892 q = 1) (hb : d209374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24892, d209374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24892, d209374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24893 q = 1) (hb : d209375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24893, d209375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24893, d209375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24894 q = 1) (hb : d209376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24894, d209376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24894, d209376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56555 (p : Pattern) (ha : d24900 p = 1) (hb : d209382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24889 q = 1) (hb : d209371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24889, d209371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56549 q ha hb
    | true =>
      simp only [d24889, d209371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24890 q = 1) (hb : d209372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24890, d209372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24890, d209372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24891 q = 1) (hb : d209373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24891, d209373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24891, d209373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24892 q = 1) (hb : d209374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24892, d209374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24892, d209374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24893 q = 1) (hb : d209375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24893, d209375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24893, d209375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24895 q = 1) (hb : d209377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24895, d209377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56552 q ha hb
    | true =>
      simp only [d24895, d209377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24896 q = 1) (hb : d209378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24896, d209378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24896, d209378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24897 q = 1) (hb : d209379 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24897, d209379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24897, d209379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24898 q = 1) (hb : d209380 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24898, d209380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24898, d209380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24899 q = 1) (hb : d209381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24899, d209381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24899, d209381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24900 q = 1) (hb : d209382 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24900, d209382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24900, d209382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56556 (p : Pattern) (ha : d24909 p = 1) (hb : d209391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24895 q = 1) (hb : d209377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24895, d209377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56552 q ha hb
    | true =>
      simp only [d24895, d209377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24896 q = 1) (hb : d209378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24896, d209378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24896, d209378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24897 q = 1) (hb : d209379 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24897, d209379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24897, d209379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24898 q = 1) (hb : d209380 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24898, d209380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24898, d209380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24899 q = 1) (hb : d209381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24899, d209381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24899, d209381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24909 q = 1) (hb : d209391 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24909, d209391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24909, d209391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56557 (p : Pattern) (ha : d24936 p = 1) (hb : d209418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24920 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
  have h2 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24921 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24922 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24923 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24926 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
  have h8 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24927 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24928 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24929 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24930 q = 1) (hb : d209412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24930, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24930, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24935 q = 1) (hb : d209417 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24935, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24935, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24936 q = 1) (hb : d209418 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24936, d209418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24936, d209418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56558 (p : Pattern) (ha : d24941 p = 1) (hb : d209423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24926 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
  have h2 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24927 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24928 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24929 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24935 q = 1) (hb : d209417 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24935, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24935, d209417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2361 q = 1) (hb : d53526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
  have h9 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2362 q = 1) (hb : d53527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2363 q = 1) (hb : d53528 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2364 q = 1) (hb : d53529 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2365 q = 1) (hb : d53530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24941 q = 1) (hb : d209423 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24941, d209423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24941, d209423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56559 (p : Pattern) (ha : d24960 p = 1) (hb : d209442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24942 q = 1) (hb : d209424 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56557 q ha hb
    | true =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56558 q ha hb
  have h2 (q : Pattern) (ha : d24943 q = 1) (hb : d209425 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24944 q = 1) (hb : d209426 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24950 q = 1) (hb : d209432 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24950, d209432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24950, d209432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24959 q = 1) (hb : d209441 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24959, d209441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24959, d209441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24960 q = 1) (hb : d209442 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24960, d209442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24960, d209442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56560 (p : Pattern) (ha : d25035 p = 1) (hb : d209453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24961 q = 1) (hb : d209443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24961, d209443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56559 q ha hb
    | true =>
      simp only [d24961, d209443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24962 q = 1) (hb : d209444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24962, d209444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24962, d209444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25032 q = 1) (hb : d209450 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25032, d209450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25032, d209450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25033 q = 1) (hb : d209451 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25033, d209451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25033, d209451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25034 q = 1) (hb : d209452 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25034, d209452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25034, d209452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25035 q = 1) (hb : d209453 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25035, d209453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25035, d209453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56561 (p : Pattern) (ha : d25041 p = 1) (hb : d209481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25036 q = 1) (hb : d209476 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25036, d209476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56560 q ha hb
    | true =>
      simp only [d25036, d209476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25037 q = 1) (hb : d209477 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25037, d209477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25037, d209477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25038 q = 1) (hb : d209478 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25038, d209478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25038, d209478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25039 q = 1) (hb : d209479 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25039, d209479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25039, d209479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25040 q = 1) (hb : d209480 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25040, d209480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25040, d209480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25041 q = 1) (hb : d209481 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25041, d209481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25041, d209481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56562 (p : Pattern) (ha : d24761 p = 1) (hb : d209298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24733 q = 1) (hb : d209270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24734 q = 1) (hb : d209271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24760 q = 1) (hb : d209297 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24760, d209297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24760, d209297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24761 q = 1) (hb : d209298 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24761, d209298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24761, d209298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56563 (p : Pattern) (ha : d24763 p = 1) (hb : d209300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24737 q = 1) (hb : d209274 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24738 q = 1) (hb : d209275 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24762 q = 1) (hb : d209299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24762, d209299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24762, d209299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24763 q = 1) (hb : d209300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24763, d209300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24763, d209300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56564 (p : Pattern) (ha : d24770 p = 1) (hb : d209307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24733 q = 1) (hb : d209270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24768 q = 1) (hb : d209305 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24768, d209305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24768, d209305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24769 q = 1) (hb : d209306 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24769, d209306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24769, d209306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24770 q = 1) (hb : d209307 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24770, d209307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24770, d209307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56565 (p : Pattern) (ha : d24773 p = 1) (hb : d209310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24737 q = 1) (hb : d209274 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24771 q = 1) (hb : d209308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24771, d209308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24771, d209308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24772 q = 1) (hb : d209309 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24772, d209309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24772, d209309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24773 q = 1) (hb : d209310 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24773, d209310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24773, d209310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56566 (p : Pattern) (ha : d24778 p = 1) (hb : d209315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d53425 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24693 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56540 q ha hb
    | true =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24694 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24695 q = 1) (hb : d209232 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24695, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24695, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24696 q = 1) (hb : d209233 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24696, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24696, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24777 q = 1) (hb : d209314 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24777, d209314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24777, d209314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24702 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24703 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d24704 q = 1) (hb : d209241 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24704, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24704, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24778 q = 1) (hb : d209315 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24778, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24778, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56567 (p : Pattern) (ha : d24784 p = 1) (hb : d209321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24779 q = 1) (hb : d209316 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24779, d209316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56566 q ha hb
    | true =>
      simp only [d24779, d209316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56543 q ha hb
  have h2 (q : Pattern) (ha : d24780 q = 1) (hb : d209317 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24780, d209317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24780, d209317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24781 q = 1) (hb : d209318 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24781, d209318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24781, d209318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24716 q = 1) (hb : d209253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24716, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56543 q ha hb
    | true =>
      simp only [d24716, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56544 q ha hb
  have h5 (q : Pattern) (ha : d24717 q = 1) (hb : d209254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24717, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24717, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24718 q = 1) (hb : d209255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24718, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24718, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24782 q = 1) (hb : d209319 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24782, d209319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24782, d209319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24720 q = 1) (hb : d209257 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56544 q ha hb
    | true =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56545 q ha hb
  have h9 (q : Pattern) (ha : d24721 q = 1) (hb : d209258 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24722 q = 1) (hb : d209259 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24723 q = 1) (hb : d209260 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24723, d209260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24723, d209260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24783 q = 1) (hb : d209320 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24783, d209320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24783, d209320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24784 q = 1) (hb : d209321 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24784, d209321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24784, d209321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56568 (p : Pattern) (ha : d24790 p = 1) (hb : d209327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24785 q = 1) (hb : d209322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24785, d209322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56567 q ha hb
    | true =>
      simp only [d24785, d209322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24786 q = 1) (hb : d209323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24786, d209323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24786, d209323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24787 q = 1) (hb : d209324 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24787, d209324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24787, d209324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24788 q = 1) (hb : d209325 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24788, d209325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24788, d209325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24789 q = 1) (hb : d209326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24789, d209326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24789, d209326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24790 q = 1) (hb : d209327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24790, d209327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24790, d209327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56569 (p : Pattern) (ha : d24845 p = 1) (hb : d209330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24702 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24702, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24703 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24703, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24710 q = 1) (hb : d209247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24710, d209247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24711 q = 1) (hb : d209248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24711, d209248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24712 q = 1) (hb : d209249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24712, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24712, d209249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5721 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9307 q ha hb
    | true =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5722 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5723 q = 1) (hb : d74449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5723, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5723, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5724 q = 1) (hb : d74450 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5724, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5724, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5725 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5725, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5725, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24845 q = 1) (hb : d209330 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24845, d209330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24845, d209330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56570 (p : Pattern) (ha : d24851 p = 1) (hb : d209336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24716 q = 1) (hb : d209253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24716, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56543 q ha hb
    | true =>
      simp only [d24716, d209253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56544 q ha hb
  have h2 (q : Pattern) (ha : d24717 q = 1) (hb : d209254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24717, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24717, d209254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24718 q = 1) (hb : d209255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24718, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24718, d209255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24720 q = 1) (hb : d209257 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56544 q ha hb
    | true =>
      simp only [d24720, d209257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56545 q ha hb
  have h5 (q : Pattern) (ha : d24721 q = 1) (hb : d209258 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24721, d209258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24722 q = 1) (hb : d209259 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24722, d209259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24723 q = 1) (hb : d209260 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24723, d209260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24723, d209260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24846 q = 1) (hb : d209331 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24846, d209331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56569 q ha hb
    | true =>
      simp only [d24846, d209331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9309 q ha hb
  have h9 (q : Pattern) (ha : d24847 q = 1) (hb : d209332 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24847, d209332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24847, d209332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24848 q = 1) (hb : d209333 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24848, d209333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24848, d209333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24849 q = 1) (hb : d209334 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24849, d209334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24849, d209334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24850 q = 1) (hb : d209335 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24850, d209335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24850, d209335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24851 q = 1) (hb : d209336 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24851, d209336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24851, d209336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56571 (p : Pattern) (ha : d24857 p = 1) (hb : d209342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24852 q = 1) (hb : d209337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24852, d209337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56570 q ha hb
    | true =>
      simp only [d24852, d209337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24853 q = 1) (hb : d209338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24853, d209338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24853, d209338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24854 q = 1) (hb : d209339 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24854, d209339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24854, d209339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24855 q = 1) (hb : d209340 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24855, d209340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24855, d209340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24856 q = 1) (hb : d209341 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24856, d209341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24856, d209341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24857 q = 1) (hb : d209342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24857, d209342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24857, d209342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56572 (p : Pattern) (ha : d209348 p = 1) (hb : d211329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24764 q = 1) (hb : d209301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24764, d209301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56562 q ha hb
    | true =>
      simp only [d24764, d209301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56563 q ha hb
  have h2 (q : Pattern) (ha : d24765 q = 1) (hb : d209302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24765, d209302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24765, d209302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24766 q = 1) (hb : d209303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24766, d209303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24766, d209303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24767 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24767, d209304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24767, d209304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24774 q = 1) (hb : d209311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24774, d209311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56564 q ha hb
    | true =>
      simp only [d24774, d209311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56565 q ha hb
  have h6 (q : Pattern) (ha : d24775 q = 1) (hb : d209312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24775, d209312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24775, d209312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24776 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24776, d209313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24776, d209313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24791 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24791, d209328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56568 q ha hb
    | true =>
      simp only [d24791, d209328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56548 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d211325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d209329, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d24858 q = 1) (hb : d209343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24858, d209343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56571 q ha hb
    | true =>
      simp only [d24858, d209343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24859 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24859, d209344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24859, d209344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d211326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d211327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d209346, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d211328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209347, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209348 q = 1) (hb : d211329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209348, d211329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209348, d211329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro56573 (p : Pattern) (ha : d24864 p = 1) (hb : d209349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24733 q = 1) (hb : d209270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24734 q = 1) (hb : d209271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24734, d209271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24760 q = 1) (hb : d209297 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24760, d209297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24760, d209297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24864 q = 1) (hb : d209349 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24864, d209349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24864, d209349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56574 (p : Pattern) (ha : d24865 p = 1) (hb : d209350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24737 q = 1) (hb : d209274 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24738 q = 1) (hb : d209275 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24738, d209275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24762 q = 1) (hb : d209299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24762, d209299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24762, d209299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24865 q = 1) (hb : d209350 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24865, d209350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24865, d209350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56575 (p : Pattern) (ha : d24870 p = 1) (hb : d209355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24733 q = 1) (hb : d209270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24733, d209270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24768 q = 1) (hb : d209305 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24768, d209305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24768, d209305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24769 q = 1) (hb : d209306 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24769, d209306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24769, d209306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24870 q = 1) (hb : d209355 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24870, d209355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24870, d209355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56576 (p : Pattern) (ha : d24871 p = 1) (hb : d209356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24731 q = 1) (hb : d209268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56547 q ha hb
    | true =>
      simp only [d24731, d209268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24732 q = 1) (hb : d209269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24732, d209269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24737 q = 1) (hb : d209274 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24737, d209274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24771 q = 1) (hb : d209308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24771, d209308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24771, d209308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24772 q = 1) (hb : d209309 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24772, d209309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24772, d209309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24871 q = 1) (hb : d209356 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24871, d209356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24871, d209356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56577 (p : Pattern) (ha : d24875 p = 1) (hb : d209360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24785 q = 1) (hb : d209322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24785, d209322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56567 q ha hb
    | true =>
      simp only [d24785, d209322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24786 q = 1) (hb : d209323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24786, d209323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24786, d209323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24727 q = 1) (hb : d209264 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56546 q ha hb
    | true =>
      simp only [d24727, d209264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24728 q = 1) (hb : d209265 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24728, d209265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24787 q = 1) (hb : d209324 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24787, d209324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24787, d209324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24788 q = 1) (hb : d209325 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24788, d209325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24788, d209325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24789 q = 1) (hb : d209326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24789, d209326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24789, d209326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24875 q = 1) (hb : d209360 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24875, d209360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24875, d209360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56578 (p : Pattern) (ha : d24881 p = 1) (hb : d209363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24852 q = 1) (hb : d209337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24852, d209337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56570 q ha hb
    | true =>
      simp only [d24852, d209337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24853 q = 1) (hb : d209338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24853, d209338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24853, d209338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24854 q = 1) (hb : d209339 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24854, d209339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24854, d209339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24855 q = 1) (hb : d209340 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24855, d209340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24855, d209340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24856 q = 1) (hb : d209341 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24856, d209341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24856, d209341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24881 q = 1) (hb : d209363 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24881, d209363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24881, d209363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56579 (p : Pattern) (ha : d209369 p = 1) (hb : d211334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24764 q = 1) (hb : d209301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24764, d209301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56562 q ha hb
    | true =>
      simp only [d24764, d209301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56563 q ha hb
  have h2 (q : Pattern) (ha : d24765 q = 1) (hb : d209302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24765, d209302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24765, d209302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24766 q = 1) (hb : d209303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24766, d209303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24766, d209303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24767 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24767, d209304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24767, d209304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24774 q = 1) (hb : d209311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24774, d209311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56564 q ha hb
    | true =>
      simp only [d24774, d209311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56565 q ha hb
  have h6 (q : Pattern) (ha : d24775 q = 1) (hb : d209312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24775, d209312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24775, d209312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24776 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24776, d209313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24776, d209313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24791 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24791, d209328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56568 q ha hb
    | true =>
      simp only [d24791, d209328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56548 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d211325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d209329, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d24858 q = 1) (hb : d209343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24858, d209343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56571 q ha hb
    | true =>
      simp only [d24858, d209343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24859 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24859, d209344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24859, d209344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d211326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d211327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d209346, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d211328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209347, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24866 q = 1) (hb : d209351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24866, d209351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56573 q ha hb
    | true =>
      simp only [d24866, d209351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56574 q ha hb
  have h17 (q : Pattern) (ha : d24867 q = 1) (hb : d209352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24867, d209352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24867, d209352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24868 q = 1) (hb : d209353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24868, d209353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d24868, d209353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d24869 q = 1) (hb : d209354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24869, d209354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24869, d209354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d24872 q = 1) (hb : d209357 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24872, d209357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56575 q ha hb
    | true =>
      simp only [d24872, d209357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56576 q ha hb
  have h21 (q : Pattern) (ha : d24873 q = 1) (hb : d209358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24873, d209358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24873, d209358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d24874 q = 1) (hb : d209359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24874, d209359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d24874, d209359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d24876 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24876, d209361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56577 q ha hb
    | true =>
      simp only [d24876, d209361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56551 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d209362 q = 1) (hb : d211330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d209362, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d24882 q = 1) (hb : d209364 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24882, d209364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56578 q ha hb
    | true =>
      simp only [d24882, d209364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d24883 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24883, d209365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d24883, d209365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d209366 q = 1) (hb : d211331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d209366, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d209367 q = 1) (hb : d211332 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209367, d211332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d209367, d211332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d209368 q = 1) (hb : d211333 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209368, d211333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d209368, d211333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d209369 q = 1) (hb : d211334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209369, d211334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209369, d211334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro56580 (p : Pattern) (ha : d209389 p = 1) (hb : d211341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24876 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24876, d209361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56577 q ha hb
    | true =>
      simp only [d24876, d209361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56551 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209362 q = 1) (hb : d211330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209362, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d24882 q = 1) (hb : d209364 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24882, d209364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56578 q ha hb
    | true =>
      simp only [d24882, d209364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24883 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24883, d209365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24883, d209365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d209366 q = 1) (hb : d211331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209366, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209387 q = 1) (hb : d211339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209387, d211339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209387, d211339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209388 q = 1) (hb : d211340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209388, d211340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209388, d211340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209389 q = 1) (hb : d211341 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d211341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d211341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56581 (p : Pattern) (ha : d24925 p = 1) (hb : d209407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2333 q = 1) (hb : d53498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24915 q = 1) (hb : d209397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24915, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24915, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56540 q ha hb
  have h8 (q : Pattern) (ha : d24693 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56540 q ha hb
    | true =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24916 q = 1) (hb : d209398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24916, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24916, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24694 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24917 q = 1) (hb : d209399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24917, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24917, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24918 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24918, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24918, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24919 q = 1) (hb : d209401 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24919, d209401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24919, d209401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24920 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
  have h15 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24921 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24922 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24923 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24924 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24924, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24924, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24925 q = 1) (hb : d209407 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24925, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24925, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56582 (p : Pattern) (ha : d24931 p = 1) (hb : d209413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24915 q = 1) (hb : d209397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24915, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24915, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56540 q ha hb
  have h2 (q : Pattern) (ha : d24693 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56540 q ha hb
    | true =>
      simp only [d24693, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24916 q = 1) (hb : d209398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24916, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24916, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24694 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24694, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24917 q = 1) (hb : d209399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24917, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24917, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24918 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24918, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24918, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24920 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
  have h8 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24921 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24922 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24923 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24924 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24924, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24924, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24926 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
  have h15 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24927 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24928 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24929 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24930 q = 1) (hb : d209412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24930, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24930, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24931 q = 1) (hb : d209413 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24931, d209413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24931, d209413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56583 (p : Pattern) (ha : d24947 p = 1) (hb : d209429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24932 q = 1) (hb : d209414 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24932, d209414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56581 q ha hb
    | true =>
      simp only [d24932, d209414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56582 q ha hb
  have h2 (q : Pattern) (ha : d24933 q = 1) (hb : d209415 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24933, d209415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24933, d209415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24934 q = 1) (hb : d209416 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24934, d209416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24934, d209416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24937 q = 1) (hb : d209419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24937, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56582 q ha hb
    | true =>
      simp only [d24937, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56557 q ha hb
  have h5 (q : Pattern) (ha : d24938 q = 1) (hb : d209420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24938, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24938, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24939 q = 1) (hb : d209421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24939, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24939, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24940 q = 1) (hb : d209422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24940, d209422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24940, d209422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24942 q = 1) (hb : d209424 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56557 q ha hb
    | true =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56558 q ha hb
  have h9 (q : Pattern) (ha : d24943 q = 1) (hb : d209425 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24944 q = 1) (hb : d209426 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24945 q = 1) (hb : d209427 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24945, d209427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24945, d209427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24946 q = 1) (hb : d209428 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24946, d209428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24946, d209428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24947 q = 1) (hb : d209429 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24947, d209429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24947, d209429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56584 (p : Pattern) (ha : d24952 p = 1) (hb : d209434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24937 q = 1) (hb : d209419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24937, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56582 q ha hb
    | true =>
      simp only [d24937, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56557 q ha hb
  have h2 (q : Pattern) (ha : d24938 q = 1) (hb : d209420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24938, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24938, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24939 q = 1) (hb : d209421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24939, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24939, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24942 q = 1) (hb : d209424 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56557 q ha hb
    | true =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56558 q ha hb
  have h5 (q : Pattern) (ha : d24943 q = 1) (hb : d209425 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24944 q = 1) (hb : d209426 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24945 q = 1) (hb : d209427 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24945, d209427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24945, d209427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24950 q = 1) (hb : d209432 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24950, d209432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24950, d209432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24951 q = 1) (hb : d209433 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24951, d209433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24951, d209433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24952 q = 1) (hb : d209434 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24952, d209434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24952, d209434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56585 (p : Pattern) (ha : d24958 p = 1) (hb : d209440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24948 q = 1) (hb : d209430 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24948, d209430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56583 q ha hb
    | true =>
      simp only [d24948, d209430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24949 q = 1) (hb : d209431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24949, d209431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24949, d209431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24953 q = 1) (hb : d209435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24953, d209435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56584 q ha hb
    | true =>
      simp only [d24953, d209435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24954 q = 1) (hb : d209436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24954, d209436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24954, d209436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24955 q = 1) (hb : d209437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24955, d209437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24955, d209437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24956 q = 1) (hb : d209438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24956, d209438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24956, d209438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24957 q = 1) (hb : d209439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24957, d209439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24957, d209439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24958 q = 1) (hb : d209440 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24958, d209440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24958, d209440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56586 (p : Pattern) (ha : d24966 p = 1) (hb : d209448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24953 q = 1) (hb : d209435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24953, d209435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56584 q ha hb
    | true =>
      simp only [d24953, d209435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24954 q = 1) (hb : d209436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24954, d209436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24954, d209436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24961 q = 1) (hb : d209443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24961, d209443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56559 q ha hb
    | true =>
      simp only [d24961, d209443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24962 q = 1) (hb : d209444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24962, d209444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24962, d209444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24963 q = 1) (hb : d209445 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24963, d209445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24963, d209445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24964 q = 1) (hb : d209446 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24964, d209446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24964, d209446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24965 q = 1) (hb : d209447 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24965, d209447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24965, d209447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24966 q = 1) (hb : d209448 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24966, d209448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24966, d209448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56587 (p : Pattern) (ha : d25012 p = 1) (hb : d209456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24920 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24920, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
  have h2 (q : Pattern) (ha : d24700 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56541 q ha hb
    | true =>
      simp only [d24700, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24921 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24921, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24701 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24701, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24922 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24922, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24923 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24923, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24926 q = 1) (hb : d209408 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24926, d209408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
  have h8 (q : Pattern) (ha : d24708 q = 1) (hb : d209245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56542 q ha hb
    | true =>
      simp only [d24708, d209245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24927 q = 1) (hb : d209409 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24927, d209409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24709 q = 1) (hb : d209246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24709, d209246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24928 q = 1) (hb : d209410 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24928, d209410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24929 q = 1) (hb : d209411 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24929, d209411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24930 q = 1) (hb : d209412 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24930, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24930, d209412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5765 q = 1) (hb : d74491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5765, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5765, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9307 q ha hb
  have h15 (q : Pattern) (ha : d5721 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9307 q ha hb
    | true =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5766 q = 1) (hb : d74492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5766, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5766, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5722 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5767 q = 1) (hb : d74493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5767, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5767, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5768 q = 1) (hb : d74494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5768, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5768, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5769 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5769, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5769, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d25012 q = 1) (hb : d209456 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25012, d209456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25012, d209456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56588 (p : Pattern) (ha : d25018 p = 1) (hb : d209462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24937 q = 1) (hb : d209419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24937, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56582 q ha hb
    | true =>
      simp only [d24937, d209419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56557 q ha hb
  have h2 (q : Pattern) (ha : d24938 q = 1) (hb : d209420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24938, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24938, d209420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24939 q = 1) (hb : d209421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24939, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24939, d209421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24942 q = 1) (hb : d209424 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56557 q ha hb
    | true =>
      simp only [d24942, d209424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56558 q ha hb
  have h5 (q : Pattern) (ha : d24943 q = 1) (hb : d209425 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24943, d209425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24944 q = 1) (hb : d209426 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24944, d209426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24945 q = 1) (hb : d209427 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24945, d209427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24945, d209427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25013 q = 1) (hb : d209457 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25013, d209457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56587 q ha hb
    | true =>
      simp only [d25013, d209457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9317 q ha hb
  have h9 (q : Pattern) (ha : d25014 q = 1) (hb : d209458 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25014, d209458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25014, d209458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25015 q = 1) (hb : d209459 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25015, d209459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25015, d209459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25016 q = 1) (hb : d209460 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25016, d209460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25016, d209460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25017 q = 1) (hb : d209461 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25017, d209461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25017, d209461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25018 q = 1) (hb : d209462 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25018, d209462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25018, d209462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56589 (p : Pattern) (ha : d25024 p = 1) (hb : d209468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25019 q = 1) (hb : d209463 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25019, d209463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56588 q ha hb
    | true =>
      simp only [d25019, d209463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25020 q = 1) (hb : d209464 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25020, d209464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25020, d209464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25021 q = 1) (hb : d209465 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25021, d209465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25021, d209465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25022 q = 1) (hb : d209466 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25022, d209466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25022, d209466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25023 q = 1) (hb : d209467 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25023, d209467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25023, d209467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25024 q = 1) (hb : d209468 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25024, d209468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25024, d209468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56590 (p : Pattern) (ha : d209474 p = 1) (hb : d211351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24967 q = 1) (hb : d209449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24967, d209449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56585 q ha hb
    | true =>
      simp only [d24967, d209449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56586 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209454 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d211347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d211347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209455, d211347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d25025 q = 1) (hb : d209469 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25025, d209469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56589 q ha hb
    | true =>
      simp only [d25025, d209469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25026 q = 1) (hb : d209470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25026, d209470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25026, d209470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d209471 q = 1) (hb : d211348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d211348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d211348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209472 q = 1) (hb : d211349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d211349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d211349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209473 q = 1) (hb : d211350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d211350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d211350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209474 q = 1) (hb : d211351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d211351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d211351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56591 (p : Pattern) (ha : d209487 p = 1) (hb : d211357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24747 q = 1) (hb : d209284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24747, d209284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24747, d209284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56550 q ha hb
  have h2 (q : Pattern) (ha : d24748 q = 1) (hb : d209285 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24748, d209285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24748, d209285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24757 q = 1) (hb : d209294 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d209294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56550 q ha hb
    | true =>
      simp only [d24757, d209294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56553 q ha hb
  have h4 (q : Pattern) (ha : d24758 q = 1) (hb : d209295 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d209295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24758, d209295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24759 q = 1) (hb : d209296 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d24759, d209296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24759, d209296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209370 q = 1) (hb : d211335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209370, d211335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56572 q ha hb
    | true =>
      simp only [d209370, d211335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56579 q ha hb
  have h7 (q : Pattern) (ha : d24901 q = 1) (hb : d209383 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24901, d209383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56554 q ha hb
    | true =>
      simp only [d24901, d209383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56555 q ha hb
  have h8 (q : Pattern) (ha : d209384 q = 1) (hb : d211336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209384, d211336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209384, d211336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d209385 q = 1) (hb : d211337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d211337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209385, d211337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d209386 q = 1) (hb : d211338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d211338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d209386, d211338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209390 q = 1) (hb : d211342 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d211342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209390, d211342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56580 q ha hb
  have h12 (q : Pattern) (ha : d24910 q = 1) (hb : d209392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24910, d209392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24910, d209392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56556 q ha hb
  have h13 (q : Pattern) (ha : d209393 q = 1) (hb : d211343 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d211343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209393, d211343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d209394 q = 1) (hb : d211344 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d211344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209394, d211344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209395 q = 1) (hb : d211345 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d211345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209395, d211345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209396 q = 1) (hb : d211346 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d211346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209396, d211346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209475 q = 1) (hb : d211352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d211352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209475, d211352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56590 q ha hb
  have h18 (q : Pattern) (ha : d25042 q = 1) (hb : d209482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25042, d209482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25042, d209482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56561 q ha hb
  have h19 (q : Pattern) (ha : d209483 q = 1) (hb : d211353 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d211353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209483, d211353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d209484 q = 1) (hb : d211354 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d211354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209484, d211354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209485 q = 1) (hb : d211355 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d211355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d209485, d211355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d209486 q = 1) (hb : d211356 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d211356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209486, d211356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209487 q = 1) (hb : d211357 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d211357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209487, d211357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro56592 (p : Pattern) (ha : d209493 p = 1) (hb : d211363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d211358 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d211358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d211358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56591 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d211359 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d211359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d211359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d211360 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d211360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d211360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d211361 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d211361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d211361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d211362 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d211362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d211362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d211363 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d211363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d211363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56593 (p : Pattern) (ha : d209499 p = 1) (hb : d211369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d211198 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56345 q ha hb
    | true =>
      simp only [d208438, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56386 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d211238 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56431 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d211239 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d211279 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d211279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d211279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56485 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d211280 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d211280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d211280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d211281 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d211281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d211281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d211321 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d211321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d211321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56539 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d211322 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d211322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d211322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d211323 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d211323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d211323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d211324 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d211324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d211324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d211364 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d211364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d211364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56592 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d211365 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d211365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d211365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d211366 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d211366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d211366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d211367 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d211367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d211367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d211368 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d211368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d211368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d211369 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d211369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d211369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro56594 (p : Pattern) (ha : d209505 p = 1) (hb : d211375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d211370 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d211370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56593 q ha hb
    | true =>
      simp only [d209500, d211370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d211371 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d211371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d211371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d211372 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d211372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d211372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d211373 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d211373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d211373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d211374 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d211374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d211374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d211375 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d211375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d211375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56595 (p : Pattern) (ha : d209511 p = 1) (hb : d211381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d211376 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d211376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56594 q ha hb
    | true =>
      simp only [d209506, d211376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d211377 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d211377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d211377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d211378 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d211378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d211378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d211379 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d211379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d211379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d211380 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d211380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d211380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d211381 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d211381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d211381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56596 (p : Pattern) (ha : d209517 p = 1) (hb : d211387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d211382 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d211382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56595 q ha hb
    | true =>
      simp only [d209512, d211382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d211383 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d211383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d211383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d211384 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d211384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d211385 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d211385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d211386 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d211386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d211387 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d211387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56597 (p : Pattern) (ha : d209523 p = 1) (hb : d211393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d211388 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56596 q ha hb
    | true =>
      simp only [d209518, d211388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d211389 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d211389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d211390 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d211390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d211391 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d211391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d211392 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d211392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d211393 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d211393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56598 (p : Pattern) (ha : d209529 p = 1) (hb : d211399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d211394 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56597 q ha hb
    | true =>
      simp only [d209524, d211394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d211395 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d211395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d211396 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d211396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d211397 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d211397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d211398 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d211398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d211399 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d211399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56599 (p : Pattern) (ha : d209535 p = 1) (hb : d211405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d211400 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56598 q ha hb
    | true =>
      simp only [d209530, d211400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d211401 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d211401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d211402 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d211402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d211403 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d211403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d211404 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d211404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d211405 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d211405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56600 (p : Pattern) (ha : d209541 p = 1) (hb : d211411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d211406 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56599 q ha hb
    | true =>
      simp only [d209536, d211406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d211407 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d211407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d211408 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d211408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d211409 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d211409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d211410 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d211410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d211411 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d211411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56601 (p : Pattern) (ha : d53655 p = 1) (hb : d208033 p = 1) : d231169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208033 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d208033 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56016 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d208033 q = 1) : d23208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d208033 q = 1) : d23209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d208033 q = 1) : d23210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d208033 q = 1) : d23211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d208033 q = 1) : d231169 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56602 (p : Pattern) (ha : d53665 p = 1) (hb : d208033 p = 1) : d231179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208033 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d208033 q = 1) : d23184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56020 q ha hb
    | true =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d208033 q = 1) : d231175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d208033 q = 1) : d231176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d208033 q = 1) : d231177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d208033 q = 1) : d231178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d208033 q = 1) : d231179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56603 (p : Pattern) (ha : d53671 p = 1) (hb : d208033 p = 1) : d231185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d208033 q = 1) : d23213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56026 q ha hb
    | true =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56027 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d208033 q = 1) : d23214 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d208033 q = 1) : d231167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d208033 q = 1) : d231168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d208033 q = 1) : d231170 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56601 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d208033 q = 1) : d231171 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d208033 q = 1) : d231172 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d208033 q = 1) : d231173 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d208033 q = 1) : d231174 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d208033 q = 1) : d231180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56602 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d208033 q = 1) : d231181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d208033 q = 1) : d231182 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d208033 q = 1) : d231183 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d208033 q = 1) : d231184 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d208033 q = 1) : d231185 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56604 (p : Pattern) (ha : d53677 p = 1) (hb : d208033 p = 1) : d231191 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d208033 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d208033 q = 1) : d231186 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56603 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d208033 q = 1) : d231187 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d208033 q = 1) : d231188 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d208033 q = 1) : d231189 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d208033 q = 1) : d231190 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d208033 q = 1) : d231191 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56605 (p : Pattern) (ha : d53680 p = 1) (hb : d208033 p = 1) : d231194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d502 q = 1) (hb : d208033 q = 1) : d23393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56055 q ha hb
    | true =>
      simp only [d502, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56056 q ha hb
  have h2 (q : Pattern) (ha : d503 q = 1) (hb : d208033 q = 1) : d23394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d208033 q = 1) : d23395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d504, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d208033 q = 1) : d23396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d208033 q = 1) : d23397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d208033 q = 1) : d231194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56606 (p : Pattern) (ha : d53691 p = 1) (hb : d208033 p = 1) : d231205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53686 q = 1) (hb : d208033 q = 1) : d231200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56086 q ha hb
    | true =>
      simp only [d53686, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56062 q ha hb
  have h2 (q : Pattern) (ha : d53687 q = 1) (hb : d208033 q = 1) : d231201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d208033 q = 1) : d231202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53688, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d208033 q = 1) : d231203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d208033 q = 1) : d231204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d208033 q = 1) : d231205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56607 (p : Pattern) (ha : d53697 p = 1) (hb : d208033 p = 1) : d231211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d208033 q = 1) : d23399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56054 q ha hb
    | true =>
      simp only [d508, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56057 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d208033 q = 1) : d23400 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d208033 q = 1) : d231192 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d208033 q = 1) : d231193 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d208033 q = 1) : d231195 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56605 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d208033 q = 1) : d231196 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d208033 q = 1) : d231197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d208033 q = 1) : d231198 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d208033 q = 1) : d231199 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d208033 q = 1) : d231206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56606 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d208033 q = 1) : d231207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d208033 q = 1) : d231208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d208033 q = 1) : d231209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d208033 q = 1) : d231210 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d208033 q = 1) : d231211 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56608 (p : Pattern) (ha : d53703 p = 1) (hb : d208033 p = 1) : d231217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d208033 q = 1) : d231212 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56607 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d208033 q = 1) : d231213 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d208033 q = 1) : d231214 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d208033 q = 1) : d231215 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d208033 q = 1) : d231216 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d208033 q = 1) : d231217 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56609 (p : Pattern) (ha : d53707 p = 1) (hb : d208033 p = 1) : d231221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d794 q = 1) (hb : d208033 q = 1) : d23666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56100 q ha hb
    | true =>
      simp only [d794, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56101 q ha hb
  have h2 (q : Pattern) (ha : d795 q = 1) (hb : d208033 q = 1) : d23667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d208033 q = 1) : d23668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d796, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d208033 q = 1) : d23669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d208033 q = 1) : d23670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d208033 q = 1) : d231221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56610 (p : Pattern) (ha : d53718 p = 1) (hb : d208033 p = 1) : d231232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53713 q = 1) (hb : d208033 q = 1) : d231227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56136 q ha hb
    | true =>
      simp only [d53713, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56109 q ha hb
  have h2 (q : Pattern) (ha : d53714 q = 1) (hb : d208033 q = 1) : d231228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d208033 q = 1) : d231229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53715, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d208033 q = 1) : d231230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d208033 q = 1) : d231231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d208033 q = 1) : d231232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56611 (p : Pattern) (ha : d53724 p = 1) (hb : d208033 p = 1) : d231238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d208033 q = 1) : d23672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d23672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56099 q ha hb
    | true =>
      simp only [d800, d23672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56102 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d208033 q = 1) : d23673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d23673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d23673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d208033 q = 1) : d231219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d208033 q = 1) : d231220 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d208033 q = 1) : d231222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56609 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d208033 q = 1) : d231223 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d208033 q = 1) : d231224 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d208033 q = 1) : d231225 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d208033 q = 1) : d231226 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d208033 q = 1) : d231233 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56610 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d208033 q = 1) : d231234 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d208033 q = 1) : d231235 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d208033 q = 1) : d231236 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d208033 q = 1) : d231237 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d208033 q = 1) : d231238 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56612 (p : Pattern) (ha : d53730 p = 1) (hb : d208033 p = 1) : d231244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d208033 q = 1) : d231239 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56611 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d208033 q = 1) : d231240 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d208033 q = 1) : d231241 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d208033 q = 1) : d231242 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d208033 q = 1) : d231243 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d208033 q = 1) : d231244 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56613 (p : Pattern) (ha : d53735 p = 1) (hb : d208033 p = 1) : d231249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1173 q = 1) (hb : d208033 q = 1) : d23988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d23988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56154 q ha hb
    | true =>
      simp only [d1173, d23988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56155 q ha hb
  have h2 (q : Pattern) (ha : d1174 q = 1) (hb : d208033 q = 1) : d23989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d208033 q = 1) : d23990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d23990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1175, d23990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d208033 q = 1) : d23991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d23991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d23991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d208033 q = 1) : d23992 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d23992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d23992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d208033 q = 1) : d231249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56614 (p : Pattern) (ha : d53746 p = 1) (hb : d208033 p = 1) : d231260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53741 q = 1) (hb : d208033 q = 1) : d231255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d231255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56190 q ha hb
    | true =>
      simp only [d53741, d231255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56163 q ha hb
  have h2 (q : Pattern) (ha : d53742 q = 1) (hb : d208033 q = 1) : d231256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d208033 q = 1) : d231257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53743, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d208033 q = 1) : d231258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d208033 q = 1) : d231259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d208033 q = 1) : d231260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56615 (p : Pattern) (ha : d53752 p = 1) (hb : d208033 p = 1) : d231266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d208033 q = 1) : d23994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d23994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56153 q ha hb
    | true =>
      simp only [d1179, d23994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56156 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d208033 q = 1) : d23995 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d23995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d23995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d208033 q = 1) : d231247 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d208033 q = 1) : d231248 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d208033 q = 1) : d231250 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56613 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d208033 q = 1) : d231251 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d208033 q = 1) : d231252 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d208033 q = 1) : d231253 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d208033 q = 1) : d231254 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d208033 q = 1) : d231261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56614 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d208033 q = 1) : d231262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d208033 q = 1) : d231263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d208033 q = 1) : d231264 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d208033 q = 1) : d231265 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d208033 q = 1) : d231266 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56616 (p : Pattern) (ha : d53758 p = 1) (hb : d208033 p = 1) : d231272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d208033 q = 1) : d231267 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56615 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d208033 q = 1) : d231268 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d208033 q = 1) : d231269 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d208033 q = 1) : d231270 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d208033 q = 1) : d231271 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d208033 q = 1) : d231272 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56617 (p : Pattern) (ha : d53764 p = 1) (hb : d208033 p = 1) : d231278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1634 q = 1) (hb : d208033 q = 1) : d24370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d24370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56208 q ha hb
    | true =>
      simp only [d1634, d24370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56209 q ha hb
  have h2 (q : Pattern) (ha : d1635 q = 1) (hb : d208033 q = 1) : d24371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d208033 q = 1) : d24372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d24372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1636, d24372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d208033 q = 1) : d24373 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d24373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d24373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d208033 q = 1) : d24374 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d24374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d24374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d208033 q = 1) : d231278 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56618 (p : Pattern) (ha : d53775 p = 1) (hb : d208033 p = 1) : d231289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53770 q = 1) (hb : d208033 q = 1) : d231284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d231284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56244 q ha hb
    | true =>
      simp only [d53770, d231284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56217 q ha hb
  have h2 (q : Pattern) (ha : d53771 q = 1) (hb : d208033 q = 1) : d231285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d208033 q = 1) : d231286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53772, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d208033 q = 1) : d231287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d208033 q = 1) : d231288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d208033 q = 1) : d231289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56619 (p : Pattern) (ha : d53781 p = 1) (hb : d208033 p = 1) : d231295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d208033 q = 1) : d24376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d24376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56207 q ha hb
    | true =>
      simp only [d1640, d24376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56210 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d208033 q = 1) : d24377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d24377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d24377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d208033 q = 1) : d231276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d208033 q = 1) : d231277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d208033 q = 1) : d231279 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56617 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d208033 q = 1) : d231280 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d208033 q = 1) : d231281 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d208033 q = 1) : d231282 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d208033 q = 1) : d231283 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d208033 q = 1) : d231290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56618 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d208033 q = 1) : d231291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d208033 q = 1) : d231292 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d208033 q = 1) : d231293 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d208033 q = 1) : d231294 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d208033 q = 1) : d231295 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56620 (p : Pattern) (ha : d53787 p = 1) (hb : d208033 p = 1) : d231301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d208033 q = 1) : d231296 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56619 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d208033 q = 1) : d231297 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d208033 q = 1) : d231298 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d208033 q = 1) : d231299 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d208033 q = 1) : d231300 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d208033 q = 1) : d231301 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56621 (p : Pattern) (ha : d53794 p = 1) (hb : d208033 p = 1) : d231308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2117 q = 1) (hb : d208033 q = 1) : d24751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d24751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56262 q ha hb
    | true =>
      simp only [d2117, d24751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56263 q ha hb
  have h2 (q : Pattern) (ha : d2118 q = 1) (hb : d208033 q = 1) : d24752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d24752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d24752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d208033 q = 1) : d24753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d24753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2119, d24753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d208033 q = 1) : d24754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d24754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d24754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d208033 q = 1) : d24755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d24755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d24755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d208033 q = 1) : d231308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56622 (p : Pattern) (ha : d53805 p = 1) (hb : d208033 p = 1) : d231319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53800 q = 1) (hb : d208033 q = 1) : d231314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d231314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56297 q ha hb
    | true =>
      simp only [d53800, d231314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56271 q ha hb
  have h2 (q : Pattern) (ha : d53801 q = 1) (hb : d208033 q = 1) : d231315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d208033 q = 1) : d231316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53802, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d208033 q = 1) : d231317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d208033 q = 1) : d231318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d208033 q = 1) : d231319 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56623 (p : Pattern) (ha : d53811 p = 1) (hb : d208033 p = 1) : d231325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d208033 q = 1) : d24757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d24757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56261 q ha hb
    | true =>
      simp only [d2123, d24757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56264 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d208033 q = 1) : d24758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d24758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d24758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d208033 q = 1) : d231306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d208033 q = 1) : d231307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d208033 q = 1) : d231309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56621 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d208033 q = 1) : d231310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d208033 q = 1) : d231311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d208033 q = 1) : d231312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d208033 q = 1) : d231313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d208033 q = 1) : d231320 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56622 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d208033 q = 1) : d231321 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d208033 q = 1) : d231322 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d208033 q = 1) : d231323 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d208033 q = 1) : d231324 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d208033 q = 1) : d231325 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56624 (p : Pattern) (ha : d53817 p = 1) (hb : d208033 p = 1) : d231331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d208033 q = 1) : d231326 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56623 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d208033 q = 1) : d231327 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d208033 q = 1) : d231328 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d208033 q = 1) : d231329 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d208033 q = 1) : d231330 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d208033 q = 1) : d231331 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56625 (p : Pattern) (ha : d53823 p = 1) (hb : d208033 p = 1) : d231337 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d208033 q = 1) : d231218 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56604 q ha hb
    | true =>
      simp only [d53704, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56608 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d208033 q = 1) : d231245 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56612 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d208033 q = 1) : d231246 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d208033 q = 1) : d231273 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56616 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d208033 q = 1) : d231274 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d208033 q = 1) : d231275 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d208033 q = 1) : d231302 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56620 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d208033 q = 1) : d231303 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d208033 q = 1) : d231304 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d208033 q = 1) : d231305 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d208033 q = 1) : d231332 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56624 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d208033 q = 1) : d231333 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d208033 q = 1) : d231334 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d208033 q = 1) : d231335 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d208033 q = 1) : d231336 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d208033 q = 1) : d231337 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro56626 (p : Pattern) (ha : d53829 p = 1) (hb : d208033 p = 1) : d231343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d208033 q = 1) : d231338 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56625 q ha hb
    | true =>
      simp only [d53824, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d208033 q = 1) : d231339 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d208033 q = 1) : d231340 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d208033 q = 1) : d231341 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d208033 q = 1) : d231342 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d208033 q = 1) : d231343 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56627 (p : Pattern) (ha : d53835 p = 1) (hb : d208033 p = 1) : d231349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d208033 q = 1) : d231344 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56626 q ha hb
    | true =>
      simp only [d53830, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d208033 q = 1) : d231345 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d208033 q = 1) : d231346 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d208033 q = 1) : d231347 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d208033 q = 1) : d231348 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d208033 q = 1) : d231349 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56628 (p : Pattern) (ha : d53841 p = 1) (hb : d231166 p = 1) : d231355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d231166 q = 1) : d231350 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d231166, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56627 q ha hb
    | true =>
      simp only [d53836, d231166, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53837 q = 1) (hb : d231166 q = 1) : d231351 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53838 q = 1) (hb : d231166 q = 1) : d231352 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53838, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53839 q = 1) (hb : d231166 q = 1) : d231353 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53839, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d53840 q = 1) (hb : d231166 q = 1) : d231354 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53840, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d53841 q = 1) (hb : d231166 q = 1) : d231355 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53841, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro56629 (p : Pattern) (ha : d53847 p = 1) (hb : d231166 p = 1) : d231361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231166 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d231166 q = 1) : d231356 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56628 q ha hb
    | true =>
      simp only [d53842, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d231166 q = 1) : d231357 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d231166 q = 1) : d231358 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d231166 q = 1) : d231359 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d231166 q = 1) : d231360 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d231166 q = 1) : d231361 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56630 (p : Pattern) (ha : d53853 p = 1) (hb : d231166 p = 1) : d231367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231166 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d231166 q = 1) : d231362 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56629 q ha hb
    | true =>
      simp only [d53848, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d231166 q = 1) : d231363 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d231166 q = 1) : d231364 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d231166 q = 1) : d231365 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d231166 q = 1) : d231366 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d231166 q = 1) : d231367 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56631 (p : Pattern) (ha : d53859 p = 1) (hb : d231166 p = 1) : d231373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231166 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d231166 q = 1) : d231368 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56630 q ha hb
    | true =>
      simp only [d53854, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d231166 q = 1) : d231369 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d231166 q = 1) : d231370 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d231166 q = 1) : d231371 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d231166 q = 1) : d231372 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d231166 q = 1) : d231373 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56632 (p : Pattern) (ha : d53865 p = 1) (hb : d231166 p = 1) : d231379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231166 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d231166 q = 1) : d231374 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56631 q ha hb
    | true =>
      simp only [d53860, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d231166 q = 1) : d231375 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d231166 q = 1) : d231376 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d231166 q = 1) : d231377 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d231166 q = 1) : d231378 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d231166 q = 1) : d231379 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56633 (p : Pattern) (ha : d23205 p = 1) (hb : d208161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23147 q = 1) (hb : d208048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d208048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56313 q ha hb
    | true =>
      simp only [d23147, d208048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d23201 q = 1) (hb : d208151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d208151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23201, d208151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23202 q = 1) (hb : d208158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d208158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23202, d208158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23203 q = 1) (hb : d208159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d208159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23203, d208159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23204 q = 1) (hb : d208160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d208160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23204, d208160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23205 q = 1) (hb : d208161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d208161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d208161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56634 (p : Pattern) (ha : d23212 p = 1) (hb : d208180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23147 q = 1) (hb : d208048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d208048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56313 q ha hb
    | true =>
      simp only [d23147, d208048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d23201 q = 1) (hb : d208151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d208151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23201, d208151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23202 q = 1) (hb : d208158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d208158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23202, d208158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23203 q = 1) (hb : d208159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d208159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23203, d208159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23204 q = 1) (hb : d208160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d208160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d208160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208166 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208170 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23154 q = 1) (hb : d208055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d208055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56315 q ha hb
    | true =>
      simp only [d23154, d208055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d23208 q = 1) (hb : d208173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d208173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23208, d208173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23209 q = 1) (hb : d208177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d208177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23209, d208177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23210 q = 1) (hb : d208178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d208178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23210, d208178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23211 q = 1) (hb : d208179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d208179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23211, d208179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23212 q = 1) (hb : d208180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d208180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23212, d208180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56635 (p : Pattern) (ha : d208189 p = 1) (hb : d231169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d208055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d208055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56315 q ha hb
    | true =>
      simp only [d23154, d208055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d23208 q = 1) (hb : d208173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d208173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23208, d208173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23209 q = 1) (hb : d208177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d208177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23209, d208177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23210 q = 1) (hb : d208187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d208187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d208187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23211 q = 1) (hb : d208188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d208188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d208188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208189 q = 1) (hb : d231169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208189, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208189, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56636 (p : Pattern) (ha : d208224 p = 1) (hb : d231179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d208085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d208085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56319 q ha hb
    | true =>
      simp only [d23184, d208085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d208214 q = 1) (hb : d231175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208214, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208214, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208220 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208221 q = 1) (hb : d231176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208221, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208221, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208222 q = 1) (hb : d231177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208222, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208222, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208223 q = 1) (hb : d231178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208223, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208223, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208224 q = 1) (hb : d231179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208224, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208224, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56637 (p : Pattern) (ha : d208230 p = 1) (hb : d231185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208116 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d208181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d208181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56633 q ha hb
    | true =>
      simp only [d23213, d208181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23214 q = 1) (hb : d208184 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d208184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d208184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208185 q = 1) (hb : d231167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208185, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208185, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208186 q = 1) (hb : d231168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208186, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208186, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208190 q = 1) (hb : d231170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208190, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208190, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56635 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208191 q = 1) (hb : d231171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208191, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208191, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208192 q = 1) (hb : d231172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208192, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208192, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208193 q = 1) (hb : d231173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208193, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208193, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208194 q = 1) (hb : d231174 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208194, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208194, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208225 q = 1) (hb : d231180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208225, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208225, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56636 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208226 q = 1) (hb : d231181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208226, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208226, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208227 q = 1) (hb : d231182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208227, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208227, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208228 q = 1) (hb : d231183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208228, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208228, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208229 q = 1) (hb : d231184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208229, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208229, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208230 q = 1) (hb : d231185 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208230, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208230, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56638 (p : Pattern) (ha : d208236 p = 1) (hb : d231191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d208097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51140 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d208098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d208099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d208100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d208101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208231 q = 1) (hb : d231186 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208231, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208231, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56637 q ha hb
  have h8 (q : Pattern) (ha : d208232 q = 1) (hb : d231187 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208232, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208232, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208233 q = 1) (hb : d231188 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208233, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208233, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208234 q = 1) (hb : d231189 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208234, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208234, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208235 q = 1) (hb : d231190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208235, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208235, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208236 q = 1) (hb : d231191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208236, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d208236, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro56639 (p : Pattern) (ha : d23388 p = 1) (hb : d208322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23383 q = 1) (hb : d208254 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d208254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56348 q ha hb
    | true =>
      simp only [d23383, d208254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56349 q ha hb
  have h5 (q : Pattern) (ha : d23384 q = 1) (hb : d208312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d208312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23384, d208312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23385 q = 1) (hb : d208319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d208319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23385, d208319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23386 q = 1) (hb : d208320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d208320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23386, d208320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23387 q = 1) (hb : d208321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d208321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23387, d208321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23388 q = 1) (hb : d208322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d208322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d208322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56640 (p : Pattern) (ha : d23398 p = 1) (hb : d208343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23383 q = 1) (hb : d208254 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d208254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56348 q ha hb
    | true =>
      simp only [d23383, d208254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56349 q ha hb
  have h4 (q : Pattern) (ha : d23384 q = 1) (hb : d208312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d208312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23384, d208312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23385 q = 1) (hb : d208319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d208319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23385, d208319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23386 q = 1) (hb : d208320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d208320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23386, d208320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23387 q = 1) (hb : d208321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d208321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d208321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208328 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208333 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23393 q = 1) (hb : d208264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d208264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56351 q ha hb
    | true =>
      simp only [d23393, d208264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56352 q ha hb
  have h13 (q : Pattern) (ha : d23394 q = 1) (hb : d208336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d208336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23394, d208336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23395 q = 1) (hb : d208340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d208340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23395, d208340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23396 q = 1) (hb : d208341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d208341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23396, d208341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23397 q = 1) (hb : d208342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d208342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23397, d208342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23398 q = 1) (hb : d208343 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d208343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23398, d208343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56641 (p : Pattern) (ha : d208363 p = 1) (hb : d231194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23393 q = 1) (hb : d208264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d208264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56351 q ha hb
    | true =>
      simp only [d23393, d208264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56352 q ha hb
  have h3 (q : Pattern) (ha : d23394 q = 1) (hb : d208336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d208336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23394, d208336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23395 q = 1) (hb : d208340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d208340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23395, d208340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23396 q = 1) (hb : d208361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d208361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d208361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23397 q = 1) (hb : d208362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d208362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d208362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208363 q = 1) (hb : d231194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208363, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208363, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56642 (p : Pattern) (ha : d208418 p = 1) (hb : d231205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208407 q = 1) (hb : d231200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208407, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56382 q hb ha
    | true =>
      simp only [d208407, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56358 q hb ha
  have h3 (q : Pattern) (ha : d208408 q = 1) (hb : d231201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208408, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208408, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208414 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208415 q = 1) (hb : d231202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208415, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208415, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208416 q = 1) (hb : d231203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208416, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208416, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208417 q = 1) (hb : d231204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208417, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208417, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208418 q = 1) (hb : d231205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208418, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208418, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56643 (p : Pattern) (ha : d208431 p = 1) (hb : d231211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d208344 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d208344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56639 q ha hb
    | true =>
      simp only [d23399, d208344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56640 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23400 q = 1) (hb : d208358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d208358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d208358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208359 q = 1) (hb : d231192 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208359, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208359, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208360 q = 1) (hb : d231193 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208360, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208360, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208364 q = 1) (hb : d231195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208364, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208364, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56641 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208366 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208367 q = 1) (hb : d231196 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208367, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208367, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208368 q = 1) (hb : d231197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208368, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208368, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208369 q = 1) (hb : d231198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208369, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208369, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208370 q = 1) (hb : d231199 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208370, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208370, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208419 q = 1) (hb : d231206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208419, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208419, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56642 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208426 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208427 q = 1) (hb : d231207 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208427, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208427, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208428 q = 1) (hb : d231208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208428, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208428, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208429 q = 1) (hb : d231209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208429, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208429, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208430 q = 1) (hb : d231210 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208430, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208430, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208431 q = 1) (hb : d231211 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208431, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208431, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56644 (p : Pattern) (ha : d208437 p = 1) (hb : d231217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208432 q = 1) (hb : d231212 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208432, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208432, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56643 q ha hb
  have h2 (q : Pattern) (ha : d208433 q = 1) (hb : d231213 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208433, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208433, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208434 q = 1) (hb : d231214 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208434, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208434, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208435 q = 1) (hb : d231215 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208435, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208435, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208436 q = 1) (hb : d231216 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208436, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208436, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208437 q = 1) (hb : d231217 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208437, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208437, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56645 (p : Pattern) (ha : d23661 p = 1) (hb : d208534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23656 q = 1) (hb : d208466 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d208466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56391 q ha hb
    | true =>
      simp only [d23656, d208466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56392 q ha hb
  have h5 (q : Pattern) (ha : d23657 q = 1) (hb : d208524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d208524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23657, d208524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23658 q = 1) (hb : d208531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d208531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23658, d208531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23659 q = 1) (hb : d208532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d208532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23659, d208532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23660 q = 1) (hb : d208533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d208533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23660, d208533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23661 q = 1) (hb : d208534 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d208534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d208534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56646 (p : Pattern) (ha : d23671 p = 1) (hb : d208555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23656 q = 1) (hb : d208466 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d208466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56391 q ha hb
    | true =>
      simp only [d23656, d208466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56392 q ha hb
  have h4 (q : Pattern) (ha : d23657 q = 1) (hb : d208524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d208524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23657, d208524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23658 q = 1) (hb : d208531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d208531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23658, d208531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23659 q = 1) (hb : d208532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d208532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23659, d208532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23660 q = 1) (hb : d208533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d208533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d208533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208545 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23666 q = 1) (hb : d208476 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d208476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56394 q ha hb
    | true =>
      simp only [d23666, d208476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56395 q ha hb
  have h13 (q : Pattern) (ha : d23667 q = 1) (hb : d208548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d208548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23667, d208548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23668 q = 1) (hb : d208552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d208552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23668, d208552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23669 q = 1) (hb : d208553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d208553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23669, d208553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23670 q = 1) (hb : d208554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d208554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23670, d208554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23671 q = 1) (hb : d208555 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d208555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23671, d208555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56647 (p : Pattern) (ha : d208575 p = 1) (hb : d231221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23666 q = 1) (hb : d208476 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d208476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56394 q ha hb
    | true =>
      simp only [d23666, d208476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56395 q ha hb
  have h3 (q : Pattern) (ha : d23667 q = 1) (hb : d208548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d208548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23667, d208548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23668 q = 1) (hb : d208552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d208552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23668, d208552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23669 q = 1) (hb : d208573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d208573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d208573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23670 q = 1) (hb : d208574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d208574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d208574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208575 q = 1) (hb : d231221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208575, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208575, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56648 (p : Pattern) (ha : d208640 p = 1) (hb : d231232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208624 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208629 q = 1) (hb : d231227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208629, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56427 q hb ha
    | true =>
      simp only [d208629, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56402 q hb ha
  have h3 (q : Pattern) (ha : d208630 q = 1) (hb : d231228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208630, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208630, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208636 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208637 q = 1) (hb : d231229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208637, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208637, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208638 q = 1) (hb : d231230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208638, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208638, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208639 q = 1) (hb : d231231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208639, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208639, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208640 q = 1) (hb : d231232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208640, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208640, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56649 (p : Pattern) (ha : d208653 p = 1) (hb : d231238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208484 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d208556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d208556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56645 q ha hb
    | true =>
      simp only [d23672, d208556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56646 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208569 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23673 q = 1) (hb : d208570 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d208570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d208570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208571 q = 1) (hb : d231219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208571, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208571, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208572 q = 1) (hb : d231220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208572, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208572, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208576 q = 1) (hb : d231222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208576, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208576, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56647 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208578 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208579 q = 1) (hb : d231223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208579, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208579, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208580 q = 1) (hb : d231224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208580, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208580, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208581 q = 1) (hb : d231225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208581, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208581, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208582 q = 1) (hb : d231226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208582, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208582, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208641 q = 1) (hb : d231233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208641, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208641, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56648 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208648 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208649 q = 1) (hb : d231234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208649, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208649, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208650 q = 1) (hb : d231235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208650, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208650, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208651 q = 1) (hb : d231236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208651, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208651, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208652 q = 1) (hb : d231237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208652, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208652, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208653 q = 1) (hb : d231238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208653, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208653, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56650 (p : Pattern) (ha : d208659 p = 1) (hb : d231244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208654 q = 1) (hb : d231239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208654, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208654, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56649 q ha hb
  have h2 (q : Pattern) (ha : d208655 q = 1) (hb : d231240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208655, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208655, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208656 q = 1) (hb : d231241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208656, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208656, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208657 q = 1) (hb : d231242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208657, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208657, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208658 q = 1) (hb : d231243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208658, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208658, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208659 q = 1) (hb : d231244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208659, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208659, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56651 (p : Pattern) (ha : d23983 p = 1) (hb : d208790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23978 q = 1) (hb : d208713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d208713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56440 q ha hb
    | true =>
      simp only [d23978, d208713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56441 q ha hb
  have h5 (q : Pattern) (ha : d23979 q = 1) (hb : d208771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d208771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23979, d208771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23980 q = 1) (hb : d208787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d208787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23980, d208787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23981 q = 1) (hb : d208788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d208788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23981, d208788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23982 q = 1) (hb : d208789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d208789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23982, d208789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23983 q = 1) (hb : d208790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d208790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d208790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56652 (p : Pattern) (ha : d23993 p = 1) (hb : d208811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23978 q = 1) (hb : d208713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d208713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56440 q ha hb
    | true =>
      simp only [d23978, d208713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56441 q ha hb
  have h4 (q : Pattern) (ha : d23979 q = 1) (hb : d208771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d208771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23979, d208771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23980 q = 1) (hb : d208787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d208787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23980, d208787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23981 q = 1) (hb : d208788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d208788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23981, d208788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23982 q = 1) (hb : d208789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d208789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d208789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208796 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23988 q = 1) (hb : d208723 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d208723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56443 q ha hb
    | true =>
      simp only [d23988, d208723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56444 q ha hb
  have h13 (q : Pattern) (ha : d23989 q = 1) (hb : d208804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d208804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23989, d208804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23990 q = 1) (hb : d208808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d208808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23990, d208808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23991 q = 1) (hb : d208809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d208809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23991, d208809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23992 q = 1) (hb : d208810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d208810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23992, d208810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23993 q = 1) (hb : d208811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23993, d208811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23993, d208811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56653 (p : Pattern) (ha : d208831 p = 1) (hb : d231249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23988 q = 1) (hb : d208723 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d208723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56443 q ha hb
    | true =>
      simp only [d23988, d208723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56444 q ha hb
  have h3 (q : Pattern) (ha : d23989 q = 1) (hb : d208804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d208804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23989, d208804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23990 q = 1) (hb : d208808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d208808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23990, d208808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23991 q = 1) (hb : d208829 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d208829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d208829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23992 q = 1) (hb : d208830 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d208830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d208830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208831 q = 1) (hb : d231249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208831, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208831, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56654 (p : Pattern) (ha : d208920 p = 1) (hb : d231260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208895 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208900 q = 1) (hb : d231255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208900, d231255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56479 q hb ha
    | true =>
      simp only [d208900, d231255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56452 q hb ha
  have h3 (q : Pattern) (ha : d208901 q = 1) (hb : d231256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208901, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208901, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208917 q = 1) (hb : d231257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208917, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208917, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208918 q = 1) (hb : d231258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208918, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208918, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208919 q = 1) (hb : d231259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208919, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208919, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208920 q = 1) (hb : d231260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208920, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208920, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56655 (p : Pattern) (ha : d208933 p = 1) (hb : d231266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23994 q = 1) (hb : d208812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d208812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56651 q ha hb
    | true =>
      simp only [d23994, d208812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56652 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208825 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23995 q = 1) (hb : d208826 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d208826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23995, d208826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208827 q = 1) (hb : d231247 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208827, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208827, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208828 q = 1) (hb : d231248 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208828, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208828, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208832 q = 1) (hb : d231250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208832, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208832, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56653 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208834 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208835 q = 1) (hb : d231251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208835, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208835, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208836 q = 1) (hb : d231252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208836, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208836, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208837 q = 1) (hb : d231253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208837, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208837, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208838 q = 1) (hb : d231254 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208838, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208838, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208921 q = 1) (hb : d231261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208921, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208921, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56654 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208928 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208929 q = 1) (hb : d231262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208929, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208929, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208930 q = 1) (hb : d231263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208930, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208930, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208931 q = 1) (hb : d231264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208931, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208931, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208932 q = 1) (hb : d231265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208932, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208932, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208933 q = 1) (hb : d231266 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208933, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208933, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56656 (p : Pattern) (ha : d208939 p = 1) (hb : d231272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208934 q = 1) (hb : d231267 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208934, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208934, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56655 q ha hb
  have h2 (q : Pattern) (ha : d208935 q = 1) (hb : d231268 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208935, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208935, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208936 q = 1) (hb : d231269 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208936, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208936, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208937 q = 1) (hb : d231270 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208937, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208937, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208938 q = 1) (hb : d231271 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208938, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208938, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208939 q = 1) (hb : d231272 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208939, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208939, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56657 (p : Pattern) (ha : d24365 p = 1) (hb : d209073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24360 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d208996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56494 q ha hb
    | true =>
      simp only [d24360, d208996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56495 q ha hb
  have h5 (q : Pattern) (ha : d24361 q = 1) (hb : d209054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d209054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24361, d209054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24362 q = 1) (hb : d209070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d209070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24362, d209070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24363 q = 1) (hb : d209071 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d209071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24363, d209071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24364 q = 1) (hb : d209072 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d209072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24364, d209072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24365 q = 1) (hb : d209073 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24365, d209073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24365, d209073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56658 (p : Pattern) (ha : d24375 p = 1) (hb : d209094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24360 q = 1) (hb : d208996 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24360, d208996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56494 q ha hb
    | true =>
      simp only [d24360, d208996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56495 q ha hb
  have h4 (q : Pattern) (ha : d24361 q = 1) (hb : d209054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d209054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24361, d209054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24362 q = 1) (hb : d209070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d209070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24362, d209070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24363 q = 1) (hb : d209071 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d209071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24363, d209071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24364 q = 1) (hb : d209072 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d209072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d209072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209079 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209084 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d24370 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d209006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56497 q ha hb
    | true =>
      simp only [d24370, d209006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56498 q ha hb
  have h13 (q : Pattern) (ha : d24371 q = 1) (hb : d209087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d209087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24371, d209087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24372 q = 1) (hb : d209091 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d209091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24372, d209091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24373 q = 1) (hb : d209092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d209092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24373, d209092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24374 q = 1) (hb : d209093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d209093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24374, d209093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24375 q = 1) (hb : d209094 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24375, d209094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24375, d209094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56659 (p : Pattern) (ha : d209114 p = 1) (hb : d231278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d24370 q = 1) (hb : d209006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d209006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56497 q ha hb
    | true =>
      simp only [d24370, d209006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56498 q ha hb
  have h3 (q : Pattern) (ha : d24371 q = 1) (hb : d209087 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d209087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24371, d209087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24372 q = 1) (hb : d209091 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d209091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24372, d209091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24373 q = 1) (hb : d209112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d209112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d209112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24374 q = 1) (hb : d209113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d209113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d209113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209114 q = 1) (hb : d231278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209114, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209114, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56660 (p : Pattern) (ha : d209203 p = 1) (hb : d231289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209178 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209183 q = 1) (hb : d231284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209183, d231284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56533 q hb ha
    | true =>
      simp only [d209183, d231284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56506 q hb ha
  have h3 (q : Pattern) (ha : d209184 q = 1) (hb : d231285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209184, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209184, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209199 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209200 q = 1) (hb : d231286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209200, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209200, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209201 q = 1) (hb : d231287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209201, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209201, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209202 q = 1) (hb : d231288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209202, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209202, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209203 q = 1) (hb : d231289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209203, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209203, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56661 (p : Pattern) (ha : d209216 p = 1) (hb : d231295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24376 q = 1) (hb : d209095 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d209095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56657 q ha hb
    | true =>
      simp only [d24376, d209095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56658 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24377 q = 1) (hb : d209109 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d209109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24377, d209109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209110 q = 1) (hb : d231276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209110, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209110, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209111 q = 1) (hb : d231277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209111, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209111, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209115 q = 1) (hb : d231279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209115, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209115, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56659 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209117 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209118 q = 1) (hb : d231280 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209118, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209118, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209119 q = 1) (hb : d231281 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209119, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209119, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209120 q = 1) (hb : d231282 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209120, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209120, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209121 q = 1) (hb : d231283 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209121, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209121, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209204 q = 1) (hb : d231290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209204, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209204, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56660 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209212 q = 1) (hb : d231291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209212, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209212, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209213 q = 1) (hb : d231292 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209213, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209213, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209214 q = 1) (hb : d231293 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209214, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209214, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209215 q = 1) (hb : d231294 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209215, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209215, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209216 q = 1) (hb : d231295 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209216, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209216, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56662 (p : Pattern) (ha : d209222 p = 1) (hb : d231301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209217 q = 1) (hb : d231296 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209217, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209217, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56661 q ha hb
  have h2 (q : Pattern) (ha : d209218 q = 1) (hb : d231297 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209218, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209218, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209219 q = 1) (hb : d231298 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209219, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209219, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209220 q = 1) (hb : d231299 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209220, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209220, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209221 q = 1) (hb : d231300 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209221, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209221, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209222 q = 1) (hb : d231301 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209222, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209222, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56663 (p : Pattern) (ha : d24746 p = 1) (hb : d209348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24741 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56548 q ha hb
    | true =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56549 q ha hb
  have h5 (q : Pattern) (ha : d24742 q = 1) (hb : d209329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d209329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24742, d209329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24743 q = 1) (hb : d209345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d209345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24743, d209345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24744 q = 1) (hb : d209346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d209346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24744, d209346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24745 q = 1) (hb : d209347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d209347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24745, d209347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24746 q = 1) (hb : d209348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24746, d209348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24746, d209348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56664 (p : Pattern) (ha : d24756 p = 1) (hb : d209369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24741 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56548 q ha hb
    | true =>
      simp only [d24741, d209278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56549 q ha hb
  have h4 (q : Pattern) (ha : d24742 q = 1) (hb : d209329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d209329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24742, d209329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24743 q = 1) (hb : d209345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d209345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24743, d209345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24744 q = 1) (hb : d209346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d209346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24744, d209346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24745 q = 1) (hb : d209347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d209347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24745, d209347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209354 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209359 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d24751 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d209288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56551 q ha hb
    | true =>
      simp only [d24751, d209288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56552 q ha hb
  have h13 (q : Pattern) (ha : d24752 q = 1) (hb : d209362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d209362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24752, d209362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24753 q = 1) (hb : d209366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d209366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24753, d209366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24754 q = 1) (hb : d209367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d209367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24754, d209367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24755 q = 1) (hb : d209368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d209368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24755, d209368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24756 q = 1) (hb : d209369 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24756, d209369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24756, d209369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56665 (p : Pattern) (ha : d209389 p = 1) (hb : d231308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d24751 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d209288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56551 q ha hb
    | true =>
      simp only [d24751, d209288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56552 q ha hb
  have h3 (q : Pattern) (ha : d24752 q = 1) (hb : d209362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d209362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24752, d209362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24753 q = 1) (hb : d209366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d209366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24753, d209366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24754 q = 1) (hb : d209387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d209387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d209387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24755 q = 1) (hb : d209388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d209388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d209388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209389 q = 1) (hb : d231308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56666 (p : Pattern) (ha : d209474 p = 1) (hb : d231319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209454 q = 1) (hb : d231314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209454, d231314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56586 q hb ha
    | true =>
      simp only [d209454, d231314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56560 q hb ha
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d231315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209455, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209470 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209471 q = 1) (hb : d231316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209472 q = 1) (hb : d231317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209473 q = 1) (hb : d231318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209474 q = 1) (hb : d231319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56667 (p : Pattern) (ha : d209487 p = 1) (hb : d231325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209296 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24757 q = 1) (hb : d209370 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d209370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56663 q ha hb
    | true =>
      simp only [d24757, d209370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56664 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24758 q = 1) (hb : d209384 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d209384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24758, d209384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209385 q = 1) (hb : d231306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209385, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209386 q = 1) (hb : d231307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209386, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209390 q = 1) (hb : d231309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209390, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56665 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209392 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209393 q = 1) (hb : d231310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209393, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209394 q = 1) (hb : d231311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209394, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209395 q = 1) (hb : d231312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209395, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209396 q = 1) (hb : d231313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209396, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209475 q = 1) (hb : d231320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209475, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56666 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209482 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209483 q = 1) (hb : d231321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209483, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209484 q = 1) (hb : d231322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209484, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209485 q = 1) (hb : d231323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209485, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209486 q = 1) (hb : d231324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209486, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209487 q = 1) (hb : d231325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209487, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56668 (p : Pattern) (ha : d209493 p = 1) (hb : d231331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d231326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56667 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d231327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d231328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d231329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d231330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d231331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56669 (p : Pattern) (ha : d209499 p = 1) (hb : d231337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d231218 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56638 q ha hb
    | true =>
      simp only [d208438, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56644 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d231245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56650 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d231246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d231273 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56656 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d231274 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d231275 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d231302 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56662 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d231303 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d231304 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d231305 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d231332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56668 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d231333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d231334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d231335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d231336 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d231337 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro56670 (p : Pattern) (ha : d209505 p = 1) (hb : d231343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d231338 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56669 q ha hb
    | true =>
      simp only [d209500, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d231339 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d231340 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d231341 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d231342 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d231343 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56671 (p : Pattern) (ha : d209511 p = 1) (hb : d231349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d231344 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56670 q ha hb
    | true =>
      simp only [d209506, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d231345 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d231346 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d231347 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d231348 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d231349 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56672 (p : Pattern) (ha : d209517 p = 1) (hb : d231355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d231350 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56671 q ha hb
    | true =>
      simp only [d209512, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d231351 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d231352 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d231353 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d231354 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d231355 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56673 (p : Pattern) (ha : d209523 p = 1) (hb : d231361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d231356 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56672 q ha hb
    | true =>
      simp only [d209518, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d231357 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d231358 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d231359 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d231360 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d231361 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56674 (p : Pattern) (ha : d209529 p = 1) (hb : d231367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d231362 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56673 q ha hb
    | true =>
      simp only [d209524, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d231363 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d231364 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d231365 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d231366 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d231367 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56675 (p : Pattern) (ha : d209535 p = 1) (hb : d231373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d231368 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56674 q ha hb
    | true =>
      simp only [d209530, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d231369 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d231370 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d231371 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d231372 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d231373 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56676 (p : Pattern) (ha : d209541 p = 1) (hb : d231379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d231374 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56675 q ha hb
    | true =>
      simp only [d209536, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d231375 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d231376 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d231377 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d231378 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d231379 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro56677 (p : Pattern) (ha : d23205 p = 1) (hb : d211124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23201 q = 1) (hb : d211120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23201, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23202 q = 1) (hb : d211121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23202, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23203 q = 1) (hb : d211122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23203, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23204 q = 1) (hb : d211123 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23204, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23205 q = 1) (hb : d211124 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56678 (p : Pattern) (ha : d23212 p = 1) (hb : d211129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23201 q = 1) (hb : d211120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23201, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23202 q = 1) (hb : d211121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23202, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23203 q = 1) (hb : d211122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23203, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23204 q = 1) (hb : d211123 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23279 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23283 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23208 q = 1) (hb : d211125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23208, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23209 q = 1) (hb : d211126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23209, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23210 q = 1) (hb : d211127 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23210, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23211 q = 1) (hb : d211128 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23211, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23212 q = 1) (hb : d211129 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23212, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56679 (p : Pattern) (ha : d211136 p = 1) (hb : d231169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23208 q = 1) (hb : d211125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23208, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23209 q = 1) (hb : d211126 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23209, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23210 q = 1) (hb : d211134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23211 q = 1) (hb : d211135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211136 q = 1) (hb : d231169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211136, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211136, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56680 (p : Pattern) (ha : d211146 p = 1) (hb : d231179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211142 q = 1) (hb : d231175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211142, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211142, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23349 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211143 q = 1) (hb : d231176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211143, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211143, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211144 q = 1) (hb : d231177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211144, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211144, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211145 q = 1) (hb : d231178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211145, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211145, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211146 q = 1) (hb : d231179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211146, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211146, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56681 (p : Pattern) (ha : d211152 p = 1) (hb : d231185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23215 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d211130 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56677 q ha hb
    | true =>
      simp only [d23213, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56678 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23214 q = 1) (hb : d211131 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211132 q = 1) (hb : d231167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211132, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211132, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211133 q = 1) (hb : d231168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211133, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211133, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211137 q = 1) (hb : d231170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211137, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211137, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56679 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211138 q = 1) (hb : d231171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211138, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211138, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211139 q = 1) (hb : d231172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211139, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211139, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211140 q = 1) (hb : d231173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211140, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211140, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211141 q = 1) (hb : d231174 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211141, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211141, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211147 q = 1) (hb : d231180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211147, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211147, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56680 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211148 q = 1) (hb : d231181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211148, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211148, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211149 q = 1) (hb : d231182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211149, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211149, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211150 q = 1) (hb : d231183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211150, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211150, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211151 q = 1) (hb : d231184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211151, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211151, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211152 q = 1) (hb : d231185 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211152, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211152, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56682 (p : Pattern) (ha : d211158 p = 1) (hb : d231191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d211115 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51189 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d211116 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d211117 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d211118 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d211119 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211153 q = 1) (hb : d231186 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211153, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211153, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56681 q ha hb
  have h8 (q : Pattern) (ha : d211154 q = 1) (hb : d231187 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211154, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211154, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211155 q = 1) (hb : d231188 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211155, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211155, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211156 q = 1) (hb : d231189 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211156, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211156, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211157 q = 1) (hb : d231190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211157, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211157, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d211158 q = 1) (hb : d231191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211158, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d211158, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro56683 (p : Pattern) (ha : d23388 p = 1) (hb : d211163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23383 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23384 q = 1) (hb : d211159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23384, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23385 q = 1) (hb : d211160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23385, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23386 q = 1) (hb : d211161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23386, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23387 q = 1) (hb : d211162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23387, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23388 q = 1) (hb : d211163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56684 (p : Pattern) (ha : d23398 p = 1) (hb : d211168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23383 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23384 q = 1) (hb : d211159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23384, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23385 q = 1) (hb : d211160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23385, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23386 q = 1) (hb : d211161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23386, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23387 q = 1) (hb : d211162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23393 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23394 q = 1) (hb : d211164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23394, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23395 q = 1) (hb : d211165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23395, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23396 q = 1) (hb : d211166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23396, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23397 q = 1) (hb : d211167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23397, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23398 q = 1) (hb : d211168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23398, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56685 (p : Pattern) (ha : d211175 p = 1) (hb : d231194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23394 q = 1) (hb : d211164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23394, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23395 q = 1) (hb : d211165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23395, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23396 q = 1) (hb : d211173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23397 q = 1) (hb : d211174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211175 q = 1) (hb : d231194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211175, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211175, d231194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56686 (p : Pattern) (ha : d211185 p = 1) (hb : d231205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211181 q = 1) (hb : d231201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211181, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211181, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23600 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211182 q = 1) (hb : d231202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211182, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211182, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211183 q = 1) (hb : d231203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211183, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211183, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211184 q = 1) (hb : d231204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211184, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211184, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211185 q = 1) (hb : d231205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211185, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211185, d231205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56687 (p : Pattern) (ha : d211191 p = 1) (hb : d231211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d211169 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56683 q ha hb
    | true =>
      simp only [d23399, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56684 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23400 q = 1) (hb : d211170 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211171 q = 1) (hb : d231192 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211171, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211171, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211172 q = 1) (hb : d231193 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211172, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211172, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211176 q = 1) (hb : d231195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211176, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211176, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56685 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211177 q = 1) (hb : d231196 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211177, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211177, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211178 q = 1) (hb : d231197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211178, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211178, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211179 q = 1) (hb : d231198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211179, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211179, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211180 q = 1) (hb : d231199 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211180, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211180, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211186 q = 1) (hb : d231206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211186, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211186, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56686 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23616 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211187 q = 1) (hb : d231207 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211187, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211187, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211188 q = 1) (hb : d231208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211188, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211188, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211189 q = 1) (hb : d231209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211189, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211189, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211190 q = 1) (hb : d231210 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211190, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211190, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211191 q = 1) (hb : d231211 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211191, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211191, d231211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56688 (p : Pattern) (ha : d211197 p = 1) (hb : d231217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211192 q = 1) (hb : d231212 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211192, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211192, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56687 q ha hb
  have h2 (q : Pattern) (ha : d211193 q = 1) (hb : d231213 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211193, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211193, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211194 q = 1) (hb : d231214 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211194, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211194, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211195 q = 1) (hb : d231215 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211195, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211195, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211196 q = 1) (hb : d231216 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211196, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211196, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211197 q = 1) (hb : d231217 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211197, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211197, d231217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56689 (p : Pattern) (ha : d23661 p = 1) (hb : d211203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23657 q = 1) (hb : d211199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23657, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23658 q = 1) (hb : d211200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23658, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23659 q = 1) (hb : d211201 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23659, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23660 q = 1) (hb : d211202 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23660, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23661 q = 1) (hb : d211203 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d211203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d211203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56690 (p : Pattern) (ha : d23671 p = 1) (hb : d211208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23656 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23657 q = 1) (hb : d211199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23657, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23658 q = 1) (hb : d211200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23658, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23659 q = 1) (hb : d211201 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23659, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23660 q = 1) (hb : d211202 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23768 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23773 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23666 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23667 q = 1) (hb : d211204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23667, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23668 q = 1) (hb : d211205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23668, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23669 q = 1) (hb : d211206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d211206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23669, d211206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23670 q = 1) (hb : d211207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d211207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23670, d211207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23671 q = 1) (hb : d211208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d211208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23671, d211208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56691 (p : Pattern) (ha : d211215 p = 1) (hb : d231221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23666 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23667 q = 1) (hb : d211204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23667, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23668 q = 1) (hb : d211205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23668, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23669 q = 1) (hb : d211213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d211213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d211213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23670 q = 1) (hb : d211214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d211214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d211214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211215 q = 1) (hb : d231221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211215, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211215, d231221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56692 (p : Pattern) (ha : d211225 p = 1) (hb : d231232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211221 q = 1) (hb : d231228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211221, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211221, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23897 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211222 q = 1) (hb : d231229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211222, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211222, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211223 q = 1) (hb : d231230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211223, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211223, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211224 q = 1) (hb : d231231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211224, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211224, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211225 q = 1) (hb : d231232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211225, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211225, d231232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56693 (p : Pattern) (ha : d211231 p = 1) (hb : d231238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d211209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d211209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56689 q ha hb
    | true =>
      simp only [d23672, d211209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56690 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23673 q = 1) (hb : d211210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d211210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d211210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211211 q = 1) (hb : d231219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211211, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211211, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211212 q = 1) (hb : d231220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211212, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211212, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211216 q = 1) (hb : d231222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211216, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211216, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56691 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23809 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211217 q = 1) (hb : d231223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211217, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211217, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211218 q = 1) (hb : d231224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211218, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211218, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211219 q = 1) (hb : d231225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211219, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211219, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211220 q = 1) (hb : d231226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211220, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211220, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211226 q = 1) (hb : d231233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211226, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211226, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56692 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23913 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211227 q = 1) (hb : d231234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211227, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211227, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211228 q = 1) (hb : d231235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211228, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211228, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211229 q = 1) (hb : d231236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211229, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211229, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211230 q = 1) (hb : d231237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211230, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211230, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211231 q = 1) (hb : d231238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211231, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211231, d231238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56694 (p : Pattern) (ha : d211237 p = 1) (hb : d231244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211232 q = 1) (hb : d231239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211232, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211232, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56693 q ha hb
  have h2 (q : Pattern) (ha : d211233 q = 1) (hb : d231240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211233, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211233, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211234 q = 1) (hb : d231241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211234, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211234, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211235 q = 1) (hb : d231242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211235, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211235, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211236 q = 1) (hb : d231243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211236, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211236, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211237 q = 1) (hb : d231244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211237, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211237, d231244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56695 (p : Pattern) (ha : d23983 p = 1) (hb : d211244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23978 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23979 q = 1) (hb : d211240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23979, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23980 q = 1) (hb : d211241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23980, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23981 q = 1) (hb : d211242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23981, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23982 q = 1) (hb : d211243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23982, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23983 q = 1) (hb : d211244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d211244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d211244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56696 (p : Pattern) (ha : d23993 p = 1) (hb : d211249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23978 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23979 q = 1) (hb : d211240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23979, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23980 q = 1) (hb : d211241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23980, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23981 q = 1) (hb : d211242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23981, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23982 q = 1) (hb : d211243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24115 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24120 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23988 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23989 q = 1) (hb : d211245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23989, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23990 q = 1) (hb : d211246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23990, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23991 q = 1) (hb : d211247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d211247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23991, d211247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23992 q = 1) (hb : d211248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d211248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23992, d211248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23993 q = 1) (hb : d211249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23993, d211249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23993, d211249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56697 (p : Pattern) (ha : d211256 p = 1) (hb : d231249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23989 q = 1) (hb : d211245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23989, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23990 q = 1) (hb : d211246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23990, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23991 q = 1) (hb : d211254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d211254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d211254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23992 q = 1) (hb : d211255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d211255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d211255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211256 q = 1) (hb : d231249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211256, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211256, d231249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56698 (p : Pattern) (ha : d211266 p = 1) (hb : d231260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24217 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211262 q = 1) (hb : d231256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211262, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211262, d231256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24276 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211263 q = 1) (hb : d231257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211263, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211263, d231257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211264 q = 1) (hb : d231258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211264, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211264, d231258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211265 q = 1) (hb : d231259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211265, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211265, d231259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211266 q = 1) (hb : d231260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211266, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211266, d231260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56699 (p : Pattern) (ha : d211272 p = 1) (hb : d231266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23994 q = 1) (hb : d211250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d211250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56695 q ha hb
    | true =>
      simp only [d23994, d211250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56696 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24147 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23995 q = 1) (hb : d211251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d211251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23995, d211251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211252 q = 1) (hb : d231247 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211252, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211252, d231247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211253 q = 1) (hb : d231248 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211253, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211253, d231248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211257 q = 1) (hb : d231250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211257, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211257, d231250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56697 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24156 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211258 q = 1) (hb : d231251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211258, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211258, d231251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211259 q = 1) (hb : d231252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211259, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211259, d231252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211260 q = 1) (hb : d231253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211260, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211260, d231253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211261 q = 1) (hb : d231254 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211261, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211261, d231254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211267 q = 1) (hb : d231261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211267, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211267, d231261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56698 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24292 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211268 q = 1) (hb : d231262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211268, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211268, d231262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211269 q = 1) (hb : d231263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211269, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211269, d231263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211270 q = 1) (hb : d231264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211270, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211270, d231264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211271 q = 1) (hb : d231265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211271, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211271, d231265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211272 q = 1) (hb : d231266 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211272, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211272, d231266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56700 (p : Pattern) (ha : d211278 p = 1) (hb : d231272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211273 q = 1) (hb : d231267 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211273, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211273, d231267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56699 q ha hb
  have h2 (q : Pattern) (ha : d211274 q = 1) (hb : d231268 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211274, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211274, d231268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211275 q = 1) (hb : d231269 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211275, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211275, d231269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211276 q = 1) (hb : d231270 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211276, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211276, d231270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211277 q = 1) (hb : d231271 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211277, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211277, d231271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211278 q = 1) (hb : d231272 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211278, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211278, d231272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56701 (p : Pattern) (ha : d24365 p = 1) (hb : d211286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24360 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24361 q = 1) (hb : d211282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24361, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24362 q = 1) (hb : d211283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24362, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24363 q = 1) (hb : d211284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24363, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24364 q = 1) (hb : d211285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24364, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24365 q = 1) (hb : d211286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24365, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24365, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56702 (p : Pattern) (ha : d24375 p = 1) (hb : d211291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24360 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24361 q = 1) (hb : d211282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24361, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24361, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24362 q = 1) (hb : d211283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24362, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24362, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24363 q = 1) (hb : d211284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24363, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24363, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24364 q = 1) (hb : d211285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24364, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24364, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24502 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d24370 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d24371 q = 1) (hb : d211287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24371, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24372 q = 1) (hb : d211288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24372, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24373 q = 1) (hb : d211289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24373, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24374 q = 1) (hb : d211290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24374, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24375 q = 1) (hb : d211291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24375, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24375, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56703 (p : Pattern) (ha : d211298 p = 1) (hb : d231278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24371 q = 1) (hb : d211287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24371, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24372 q = 1) (hb : d211288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24372, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24373 q = 1) (hb : d211296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24374 q = 1) (hb : d211297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211298 q = 1) (hb : d231278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211298, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211298, d231278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56704 (p : Pattern) (ha : d211308 p = 1) (hb : d231289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211304 q = 1) (hb : d231285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211304, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211304, d231285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24658 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211305 q = 1) (hb : d231286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211305, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211305, d231286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211306 q = 1) (hb : d231287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211306, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211306, d231287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211307 q = 1) (hb : d231288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211307, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211307, d231288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211308 q = 1) (hb : d231289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211308, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211308, d231289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56705 (p : Pattern) (ha : d211314 p = 1) (hb : d231295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24376 q = 1) (hb : d211292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56701 q ha hb
    | true =>
      simp only [d24376, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56702 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24377 q = 1) (hb : d211293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24377, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211294 q = 1) (hb : d231276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211294, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211294, d231276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211295 q = 1) (hb : d231277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211295, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211295, d231277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211299 q = 1) (hb : d231279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211299, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211299, d231279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56703 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24538 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211300 q = 1) (hb : d231280 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211300, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211300, d231280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211301 q = 1) (hb : d231281 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211301, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211301, d231281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211302 q = 1) (hb : d231282 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211302, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211302, d231282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211303 q = 1) (hb : d231283 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211303, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211303, d231283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211309 q = 1) (hb : d231290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211309, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211309, d231290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56704 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24674 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211310 q = 1) (hb : d231291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211310, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211310, d231291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211311 q = 1) (hb : d231292 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211311, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211311, d231292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211312 q = 1) (hb : d231293 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211312, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211312, d231293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211313 q = 1) (hb : d231294 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211313, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211313, d231294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211314 q = 1) (hb : d231295 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211314, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211314, d231295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56706 (p : Pattern) (ha : d211320 p = 1) (hb : d231301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211315 q = 1) (hb : d231296 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211315, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211315, d231296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56705 q ha hb
  have h2 (q : Pattern) (ha : d211316 q = 1) (hb : d231297 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211316, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211316, d231297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211317 q = 1) (hb : d231298 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211317, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211317, d231298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211318 q = 1) (hb : d231299 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211318, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211318, d231299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211319 q = 1) (hb : d231300 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211319, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211319, d231300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211320 q = 1) (hb : d231301 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211320, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211320, d231301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56707 (p : Pattern) (ha : d24746 p = 1) (hb : d211329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24741 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24742 q = 1) (hb : d211325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24742, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24743 q = 1) (hb : d211326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24743, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24744 q = 1) (hb : d211327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24744, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d24745 q = 1) (hb : d211328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24745, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24746 q = 1) (hb : d211329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24746, d211329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24746, d211329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56708 (p : Pattern) (ha : d24756 p = 1) (hb : d211334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24741 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d24742 q = 1) (hb : d211325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24742, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24742, d211325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d24743 q = 1) (hb : d211326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24743, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24743, d211326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24744 q = 1) (hb : d211327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24744, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24744, d211327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24745 q = 1) (hb : d211328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24745, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24745, d211328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24874 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d24751 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d24752 q = 1) (hb : d211330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24752, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d24753 q = 1) (hb : d211331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24753, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d24754 q = 1) (hb : d211332 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d211332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24754, d211332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24755 q = 1) (hb : d211333 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d211333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24755, d211333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d24756 q = 1) (hb : d211334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24756, d211334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d24756, d211334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro56709 (p : Pattern) (ha : d211341 p = 1) (hb : d231308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24751 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24752 q = 1) (hb : d211330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24752, d211330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24753 q = 1) (hb : d211331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24753, d211331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24754 q = 1) (hb : d211339 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d211339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d211339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24755 q = 1) (hb : d211340 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d211340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d211340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211341 q = 1) (hb : d231308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211341, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211341, d231308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro56710 (p : Pattern) (ha : d211351 p = 1) (hb : d231319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211347 q = 1) (hb : d231315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211347, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211347, d231315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211348 q = 1) (hb : d231316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211348, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211348, d231316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211349 q = 1) (hb : d231317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211349, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211349, d231317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211350 q = 1) (hb : d231318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211350, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211350, d231318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211351 q = 1) (hb : d231319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211351, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211351, d231319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56711 (p : Pattern) (ha : d211357 p = 1) (hb : d231325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24759 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24757 q = 1) (hb : d211335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d211335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56707 q ha hb
    | true =>
      simp only [d24757, d211335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56708 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d24758 q = 1) (hb : d211336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d211336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24758, d211336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211337 q = 1) (hb : d231306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211337, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211337, d231306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211338 q = 1) (hb : d231307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211338, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211338, d231307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211342 q = 1) (hb : d231309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211342, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211342, d231309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56709 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24910 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211343 q = 1) (hb : d231310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211343, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211343, d231310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211344 q = 1) (hb : d231311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211344, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211344, d231311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211345 q = 1) (hb : d231312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211345, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211345, d231312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211346 q = 1) (hb : d231313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211346, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211346, d231313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211352 q = 1) (hb : d231320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211352, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211352, d231320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56710 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25042 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211353 q = 1) (hb : d231321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211353, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211353, d231321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211354 q = 1) (hb : d231322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211354, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211354, d231322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211355 q = 1) (hb : d231323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211355, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211355, d231323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211356 q = 1) (hb : d231324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211356, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211356, d231324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211357 q = 1) (hb : d231325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211357, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211357, d231325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56712 (p : Pattern) (ha : d211363 p = 1) (hb : d231331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211358 q = 1) (hb : d231326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211358, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211358, d231326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56711 q ha hb
  have h2 (q : Pattern) (ha : d211359 q = 1) (hb : d231327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211359, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211359, d231327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211360 q = 1) (hb : d231328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211360, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211360, d231328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211361 q = 1) (hb : d231329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211361, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211361, d231329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211362 q = 1) (hb : d231330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211362, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211362, d231330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211363 q = 1) (hb : d231331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211363, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211363, d231331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56713 (p : Pattern) (ha : d211369 p = 1) (hb : d231337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d211198 q = 1) (hb : d231218 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211198, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56682 q ha hb
    | true =>
      simp only [d211198, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56688 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211238 q = 1) (hb : d231245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211238, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211238, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56694 q ha hb
  have h3 (q : Pattern) (ha : d211239 q = 1) (hb : d231246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211239, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211239, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211279 q = 1) (hb : d231273 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211279, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211279, d231273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56700 q ha hb
  have h5 (q : Pattern) (ha : d211280 q = 1) (hb : d231274 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211280, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211280, d231274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211281 q = 1) (hb : d231275 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211281, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211281, d231275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211321 q = 1) (hb : d231302 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211321, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211321, d231302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56706 q ha hb
  have h8 (q : Pattern) (ha : d211322 q = 1) (hb : d231303 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211322, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211322, d231303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211323 q = 1) (hb : d231304 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211323, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211323, d231304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211324 q = 1) (hb : d231305 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211324, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211324, d231305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211364 q = 1) (hb : d231332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211364, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211364, d231332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56712 q ha hb
  have h12 (q : Pattern) (ha : d211365 q = 1) (hb : d231333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211365, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211365, d231333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211366 q = 1) (hb : d231334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211366, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211366, d231334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211367 q = 1) (hb : d231335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211367, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211367, d231335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211368 q = 1) (hb : d231336 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d211368, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211368, d231336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d211369 q = 1) (hb : d231337 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d211369, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211369, d231337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro56714 (p : Pattern) (ha : d211375 p = 1) (hb : d231343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211370 q = 1) (hb : d231338 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d211370, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56713 q ha hb
    | true =>
      simp only [d211370, d231338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211371 q = 1) (hb : d231339 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d211371, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211371, d231339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211372 q = 1) (hb : d231340 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d211372, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211372, d231340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211373 q = 1) (hb : d231341 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d211373, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211373, d231341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211374 q = 1) (hb : d231342 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d211374, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211374, d231342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211375 q = 1) (hb : d231343 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d211375, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211375, d231343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56715 (p : Pattern) (ha : d211381 p = 1) (hb : d231349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211376 q = 1) (hb : d231344 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d211376, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56714 q ha hb
    | true =>
      simp only [d211376, d231344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211377 q = 1) (hb : d231345 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d211377, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211377, d231345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211378 q = 1) (hb : d231346 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d211378, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211378, d231346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211379 q = 1) (hb : d231347 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d211379, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211379, d231347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211380 q = 1) (hb : d231348 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d211380, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211380, d231348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211381 q = 1) (hb : d231349 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d211381, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211381, d231349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56716 (p : Pattern) (ha : d211387 p = 1) (hb : d231355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211382 q = 1) (hb : d231350 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d211382, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56715 q ha hb
    | true =>
      simp only [d211382, d231350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211383 q = 1) (hb : d231351 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d211383, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211383, d231351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211384 q = 1) (hb : d231352 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d211384, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211384, d231352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211385 q = 1) (hb : d231353 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d211385, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211385, d231353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211386 q = 1) (hb : d231354 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d211386, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211386, d231354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211387 q = 1) (hb : d231355 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d211387, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211387, d231355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56717 (p : Pattern) (ha : d211393 p = 1) (hb : d231361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211388 q = 1) (hb : d231356 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d211388, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56716 q ha hb
    | true =>
      simp only [d211388, d231356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211389 q = 1) (hb : d231357 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d211389, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211389, d231357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211390 q = 1) (hb : d231358 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d211390, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211390, d231358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211391 q = 1) (hb : d231359 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d211391, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211391, d231359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211392 q = 1) (hb : d231360 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d211392, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211392, d231360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211393 q = 1) (hb : d231361 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d211393, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211393, d231361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56718 (p : Pattern) (ha : d211399 p = 1) (hb : d231367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211394 q = 1) (hb : d231362 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d211394, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56717 q ha hb
    | true =>
      simp only [d211394, d231362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211395 q = 1) (hb : d231363 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d211395, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211395, d231363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211396 q = 1) (hb : d231364 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d211396, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211396, d231364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211397 q = 1) (hb : d231365 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d211397, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211397, d231365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211398 q = 1) (hb : d231366 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d211398, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211398, d231366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211399 q = 1) (hb : d231367 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d211399, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211399, d231367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56719 (p : Pattern) (ha : d211405 p = 1) (hb : d231373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211400 q = 1) (hb : d231368 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d211400, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56718 q ha hb
    | true =>
      simp only [d211400, d231368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211401 q = 1) (hb : d231369 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d211401, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211401, d231369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211402 q = 1) (hb : d231370 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d211402, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211402, d231370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211403 q = 1) (hb : d231371 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d211403, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211403, d231371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211404 q = 1) (hb : d231372 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d211404, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211404, d231372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211405 q = 1) (hb : d231373 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d211405, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211405, d231373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56720 (p : Pattern) (ha : d211411 p = 1) (hb : d231379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211406 q = 1) (hb : d231374 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d211406, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56719 q ha hb
    | true =>
      simp only [d211406, d231374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211407 q = 1) (hb : d231375 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d211407, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211407, d231375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211408 q = 1) (hb : d231376 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d211408, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211408, d231376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211409 q = 1) (hb : d231377 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d211409, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211409, d231377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211410 q = 1) (hb : d231378 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d211410, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211410, d231378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211411 q = 1) (hb : d231379 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d211411, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211411, d231379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56721 (p : Pattern) (ha : d24 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro56722 (p : Pattern) (ha : d30 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
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
theorem andIntro56723 (p : Pattern) (ha : d36 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56724 (p : Pattern) (ha : d42 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56725 (p : Pattern) (ha : d48 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56726 (p : Pattern) (ha : d49 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56727 (p : Pattern) (ha : d55 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56728 (p : Pattern) (ha : d60 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56729 (p : Pattern) (ha : d71 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
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
theorem andIntro56730 (p : Pattern) (ha : d77 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56731 (p : Pattern) (ha : d83 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56730 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56732 (p : Pattern) (ha : d89 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56731 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56733 (p : Pattern) (ha : d95 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56725 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56727 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56728 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56732 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56734 (p : Pattern) (ha : d104 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56735 (p : Pattern) (ha : d111 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56736 (p : Pattern) (ha : d213 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56737 (p : Pattern) (ha : d138 p = 1) (hb : d231381 p = 1) : d29114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136 q = 1) (hb : d231381 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d231381, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136, d231381, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137 q = 1) (hb : d231381 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d138 q = 1) (hb : d231381 q = 1) : d29114 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56738 (p : Pattern) (ha : d144 p = 1) (hb : d231381 p = 1) : d234713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d231381 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56737 q ha hb
    | true =>
      simp only [d139, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d231381 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d231381 q = 1) : d29117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d231381 q = 1) : d29118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d143 q = 1) (hb : d231381 q = 1) : d29119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d144 q = 1) (hb : d231381 q = 1) : d234713 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d234713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144, d234713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56739 (p : Pattern) (ha : d150 p = 1) (hb : d231381 p = 1) : d234719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d231381 q = 1) : d234714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56738 q ha hb
    | true =>
      simp only [d145, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d231381 q = 1) : d234715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d231381 q = 1) : d234716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d231381 q = 1) : d234717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d149 q = 1) (hb : d231381 q = 1) : d234718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d234718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149, d234718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150 q = 1) (hb : d231381 q = 1) : d234719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d234719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150, d234719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56740 (p : Pattern) (ha : d203 p = 1) (hb : d231381 p = 1) : d234732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56739 q ha hb
    | true =>
      simp only [d151, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d203 q = 1) (hb : d231381 q = 1) : d234732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d203, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56741 (p : Pattern) (ha : d4349 p = 1) (hb : d231381 p = 1) : d234743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56740 q ha hb
    | true =>
      simp only [d204, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
  have h2 (q : Pattern) (ha : d4340 q = 1) (hb : d231381 q = 1) : d234734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4340, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d231381 q = 1) : d234735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d234735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4341, d234735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d231381 q = 1) : d234736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d234736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d234736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d231381 q = 1) : d234737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d234737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d234737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d231381 q = 1) : d234743 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d234743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d234743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56742 (p : Pattern) (ha : d231 p = 1) (hb : d231381 p = 1) : d234749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d231381 q = 1) : d29395 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56737 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d231381 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56737 q ha hb
    | true =>
      simp only [d139, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d231381 q = 1) : d29396 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d231381 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d231381 q = 1) : d29397 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d231381 q = 1) : d29398 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d230 q = 1) (hb : d231381 q = 1) : d29399 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231 q = 1) (hb : d231381 q = 1) : d234749 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d234749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231, d234749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56743 (p : Pattern) (ha : d237 p = 1) (hb : d231381 p = 1) : d234755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d231381 q = 1) : d234750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56742 q ha hb
    | true =>
      simp only [d232, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d231381 q = 1) : d234751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d231381 q = 1) : d234752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d231381 q = 1) : d234753 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d236 q = 1) (hb : d231381 q = 1) : d234754 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d234754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236, d234754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237 q = 1) (hb : d231381 q = 1) : d234755 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d234755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237, d234755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56744 (p : Pattern) (ha : d243 p = 1) (hb : d231381 p = 1) : d234761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d231381 q = 1) : d234756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56743 q ha hb
    | true =>
      simp only [d238, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d231381 q = 1) : d234757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56730 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d240 q = 1) (hb : d231381 q = 1) : d234758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241 q = 1) (hb : d231381 q = 1) : d234759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d242 q = 1) (hb : d231381 q = 1) : d234760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d243 q = 1) (hb : d231381 q = 1) : d234761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56745 (p : Pattern) (ha : d4359 p = 1) (hb : d231381 p = 1) : d234767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d231381 q = 1) : d234762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56744 q ha hb
    | true =>
      simp only [d244, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56731 q ha hb
  have h2 (q : Pattern) (ha : d4355 q = 1) (hb : d231381 q = 1) : d234763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d234763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, d234763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56731 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d231381 q = 1) : d234764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d234764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4356, d234764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d231381 q = 1) : d234765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d234765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d234765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d231381 q = 1) : d234766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d234766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d234766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d231381 q = 1) : d234767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d234767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d234767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56746 (p : Pattern) (ha : d116 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56747 (p : Pattern) (ha : d123 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
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
theorem andIntro56748 (p : Pattern) (ha : d156 p = 1) (hb : d231381 p = 1) : d234725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56739 q ha hb
    | true =>
      simp only [d151, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156 q = 1) (hb : d231381 q = 1) : d234725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56749 (p : Pattern) (ha : d51643 p = 1) (hb : d231381 p = 1) : d234731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56746 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56747 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56748 q ha hb
    | true =>
      simp only [d157, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d231381 q = 1) : d234727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d231381 q = 1) : d234728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d234728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, d234728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d231381 q = 1) : d234729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d234729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d234729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d231381 q = 1) : d234730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d234730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d234730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51643 q = 1) (hb : d231381 q = 1) : d234731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d234731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d234731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
