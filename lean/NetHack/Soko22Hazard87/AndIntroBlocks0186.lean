import NetHack.Soko22Hazard87.AndIntroBlocks0185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro46500 (p : Pattern) (ha : d21154 p = 1) (hb : d116753 p = 1) : d196092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d116753 q = 1) : d196083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d116753 q = 1) : d196084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21154 q = 1) (hb : d116753 q = 1) : d196092 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21154, d196092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21154, d196092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46501 (p : Pattern) (ha : d21155 p = 1) (hb : d116753 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21155 q = 1) (hb : d116753 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21155, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21155, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46502 (p : Pattern) (ha : d21161 p = 1) (hb : d116753 p = 1) : d196153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d116753 q = 1) : d196086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46497 q ha hb
    | true =>
      simp only [d21146, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46498 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d116753 q = 1) : d196142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d196142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d196142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d116753 q = 1) : d196143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d196143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d196143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d116753 q = 1) : d196144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d196144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d196144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d116753 q = 1) : d196145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d196145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d196145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21156 q = 1) (hb : d116753 q = 1) : d196093 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46500 q ha hb
    | true =>
      simp only [d21156, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46501 q ha hb
  have h7 (q : Pattern) (ha : d21157 q = 1) (hb : d116753 q = 1) : d196149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d196149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d196149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21158 q = 1) (hb : d116753 q = 1) : d196150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d196150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21158, d196150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21159 q = 1) (hb : d116753 q = 1) : d196151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d196151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d196151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21160 q = 1) (hb : d116753 q = 1) : d196152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d196152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d196152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21161 q = 1) (hb : d116753 q = 1) : d196153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d196153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21161, d196153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46503 (p : Pattern) (ha : d21288 p = 1) (hb : d116753 p = 1) : d196214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d116753 q = 1) : d196086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46497 q ha hb
    | true =>
      simp only [d21146, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46498 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d116753 q = 1) : d196142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d196142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d196142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d116753 q = 1) : d196143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d196143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d196143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d116753 q = 1) : d196144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d196144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d196144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d116753 q = 1) : d196145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d196145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d196145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21283 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46498 q ha hb
    | true =>
      simp only [d21283, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21284 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21285 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21285, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21286 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21287 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21288 q = 1) (hb : d116753 q = 1) : d196214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21288, d196214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21288, d196214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46504 (p : Pattern) (ha : d21294 p = 1) (hb : d116753 p = 1) : d120143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21283 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46498 q ha hb
    | true =>
      simp only [d21283, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21284 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21285 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21285, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21286 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21287 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21289 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46501 q ha hb
    | true =>
      simp only [d21289, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21290 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21291 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21291, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21292 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21293 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21294 q = 1) (hb : d116753 q = 1) : d120143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21294, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21294, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46505 (p : Pattern) (ha : d21303 p = 1) (hb : d116753 p = 1) : d120334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21289 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46501 q ha hb
    | true =>
      simp only [d21289, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21290 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21291 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21291, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21292 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21293 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21303 q = 1) (hb : d116753 q = 1) : d120334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21303, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21303, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46506 (p : Pattern) (ha : d21342 p = 1) (hb : d116753 p = 1) : d120108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20933 q = 1) (hb : d116752 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46467 q ha hb
    | true =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h2 (q : Pattern) (ha : d20934 q = 1) (hb : d116752 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20935 q = 1) (hb : d116752 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21332 q = 1) (hb : d116753 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21332, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21341 q = 1) (hb : d116753 q = 1) : d120107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21341, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21341, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21342 q = 1) (hb : d116753 q = 1) : d120108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21342, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21342, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46507 (p : Pattern) (ha : d21398 p = 1) (hb : d116753 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21343 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46506 q ha hb
    | true =>
      simp only [d21343, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21344 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21395 q = 1) (hb : d116753 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21395, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21395, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21396 q = 1) (hb : d116753 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21396, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21396, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21397 q = 1) (hb : d116753 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21397, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21397, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21398 q = 1) (hb : d116753 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21398, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21398, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46508 (p : Pattern) (ha : d21404 p = 1) (hb : d116753 p = 1) : d120378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21399 q = 1) (hb : d116753 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21399, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46507 q ha hb
    | true =>
      simp only [d21399, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21400 q = 1) (hb : d116753 q = 1) : d120374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21400, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21400, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21401 q = 1) (hb : d116753 q = 1) : d120375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21401, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21401, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21402 q = 1) (hb : d116753 q = 1) : d120376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21402, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21402, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21403 q = 1) (hb : d116753 q = 1) : d120377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21403, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21403, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21404 q = 1) (hb : d116753 q = 1) : d120378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21404, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21404, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46509 (p : Pattern) (ha : d21166 p = 1) (hb : d116753 p = 1) : d196158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d116753 q = 1) : d196083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d116753 q = 1) : d196157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d196157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d196157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21166 q = 1) (hb : d116753 q = 1) : d196158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21166, d196158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21166, d196158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46510 (p : Pattern) (ha : d21168 p = 1) (hb : d116753 p = 1) : d120148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21168 q = 1) (hb : d116753 q = 1) : d120148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21168, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21168, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46511 (p : Pattern) (ha : d21175 p = 1) (hb : d116753 p = 1) : d196165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d116753 q = 1) : d196163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d196163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d196163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d116753 q = 1) : d196164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d196164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d196164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21175 q = 1) (hb : d116753 q = 1) : d196165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21175, d196165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21175, d196165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46512 (p : Pattern) (ha : d21178 p = 1) (hb : d116753 p = 1) : d120155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21178 q = 1) (hb : d116753 q = 1) : d120155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21178, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21178, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46513 (p : Pattern) (ha : d21194 p = 1) (hb : d116752 p = 1) : d196169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21187 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21193 q = 1) (hb : d116750 q = 1) : d21193 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21194 q = 1) (hb : d116752 q = 1) : d196169 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21194, d116752, d196169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21194, d116752, d196169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46514 (p : Pattern) (ha : d21204 p = 1) (hb : d116753 p = 1) : d196175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21195 q = 1) (hb : d116752 q = 1) : d196170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21195, d196170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46513 q ha hb
    | true =>
      simp only [d21195, d196170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46477 q ha hb
  have h2 (q : Pattern) (ha : d21196 q = 1) (hb : d116752 q = 1) : d196171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21196, d196171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21196, d196171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21197 q = 1) (hb : d116752 q = 1) : d196172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21197, d196172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21197, d196172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21201 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21202 q = 1) (hb : d116753 q = 1) : d196173 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21202, d116753, d196173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21202, d116753, d196173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d20997 q = 1) (hb : d116752 q = 1) : d196074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46477 q ha hb
    | true =>
      simp only [d20997, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46460 q ha hb
  have h7 (q : Pattern) (ha : d20998 q = 1) (hb : d116752 q = 1) : d196075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20999 q = 1) (hb : d116752 q = 1) : d196076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d20896 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21000 q = 1) (hb : d116753 q = 1) : d196077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d116753, d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21000, d116753, d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21203 q = 1) (hb : d116753 q = 1) : d196174 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21203, d196174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21203, d196174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21204 q = 1) (hb : d116753 q = 1) : d196175 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21204, d196175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21204, d196175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46515 (p : Pattern) (ha : d21210 p = 1) (hb : d116753 p = 1) : d196181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d116753 q = 1) : d196176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46514 q ha hb
    | true =>
      simp only [d21205, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d116753 q = 1) : d196177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d116753 q = 1) : d196178 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d196178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d196178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d116753 q = 1) : d196179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d196179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d196179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d116753 q = 1) : d196180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d196180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d196180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21210 q = 1) (hb : d116753 q = 1) : d196181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21210, d196181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21210, d196181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46516 (p : Pattern) (ha : d21251 p = 1) (hb : d116753 p = 1) : d196187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d116753 q = 1) : d196184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d196184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d196184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d116753 q = 1) : d196185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d196185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d196185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d116753 q = 1) : d196186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d196186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d196186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21251 q = 1) (hb : d116753 q = 1) : d196187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21251, d196187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21251, d196187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46517 (p : Pattern) (ha : d116753 p = 1) (hb : d150078 p = 1) : d196193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d116753 q = 1) : d196159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d196159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46509 q ha hb
    | true =>
      simp only [d21169, d196159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46510 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d116753 q = 1) : d196160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d196160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d196160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d116753 q = 1) : d196161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d196161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d196161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d116753 q = 1) : d196162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d196162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d196162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d116753 q = 1) : d196166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d196166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46511 q ha hb
    | true =>
      simp only [d21179, d196166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46512 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d116753 q = 1) : d196167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d196167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d196167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d116753 q = 1) : d196168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d196168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d196168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d116753 q = 1) : d196182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d196182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46515 q ha hb
    | true =>
      simp only [d21211, d196182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46497 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150074 q = 1) : d196183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d196183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150074, d196183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d116753 q = 1) : d196188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d196188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46516 q ha hb
    | true =>
      simp only [d21252, d196188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d116753 q = 1) : d196189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d196189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d196189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150075 q = 1) : d196190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d196190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d196190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150076 q = 1) : d196191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d196191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150076, d196191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150077 q = 1) : d196192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d196192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150077, d196192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150078 q = 1) : d196193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d196193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150078, d196193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46518 (p : Pattern) (ha : d21258 p = 1) (hb : d116753 p = 1) : d196194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d116753 q = 1) : d196083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d116753 q = 1) : d196157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d196157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d196157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21258 q = 1) (hb : d116753 q = 1) : d196194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21258, d196194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21258, d196194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46519 (p : Pattern) (ha : d21259 p = 1) (hb : d116753 p = 1) : d120178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21259 q = 1) (hb : d116753 q = 1) : d120178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21259, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21259, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46520 (p : Pattern) (ha : d21264 p = 1) (hb : d116753 p = 1) : d196199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d116753 q = 1) : d196163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d196163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d196163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d116753 q = 1) : d196164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d196164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d196164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21264 q = 1) (hb : d116753 q = 1) : d196199 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21264, d196199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21264, d196199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46521 (p : Pattern) (ha : d21265 p = 1) (hb : d116753 p = 1) : d120183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21265 q = 1) (hb : d116753 q = 1) : d120183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21265, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21265, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46522 (p : Pattern) (ha : d21269 p = 1) (hb : d116753 p = 1) : d196203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d116753 q = 1) : d196176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46514 q ha hb
    | true =>
      simp only [d21205, d196176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d116753 q = 1) : d196177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d196177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d116753 q = 1) : d196178 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d196178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d196178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d116753 q = 1) : d196179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d196179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d196179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d116753 q = 1) : d196180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d196180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d196180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21269 q = 1) (hb : d116753 q = 1) : d196203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21269, d196203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21269, d196203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46523 (p : Pattern) (ha : d21275 p = 1) (hb : d116753 p = 1) : d196206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d116753 q = 1) : d196184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d196184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d196184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d116753 q = 1) : d196185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d196185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d196185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d116753 q = 1) : d196186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d196186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d196186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21275 q = 1) (hb : d116753 q = 1) : d196206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21275, d196206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21275, d196206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46524 (p : Pattern) (ha : d116753 p = 1) (hb : d150083 p = 1) : d196212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d116753 q = 1) : d196159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d196159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46509 q ha hb
    | true =>
      simp only [d21169, d196159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46510 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d116753 q = 1) : d196160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d196160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d196160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d116753 q = 1) : d196161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d196161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d196161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d116753 q = 1) : d196162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d196162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d196162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d116753 q = 1) : d196166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d196166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46511 q ha hb
    | true =>
      simp only [d21179, d196166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46512 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d116753 q = 1) : d196167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d196167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d196167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d116753 q = 1) : d196168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d196168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d196168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d116753 q = 1) : d196182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d196182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46515 q ha hb
    | true =>
      simp only [d21211, d196182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46497 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150074 q = 1) : d196183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d196183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150074, d196183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d116753 q = 1) : d196188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d196188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46516 q ha hb
    | true =>
      simp only [d21252, d196188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d116753 q = 1) : d196189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d196189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d196189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150075 q = 1) : d196190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d196190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d196190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150076 q = 1) : d196191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d196191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150076, d196191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150077 q = 1) : d196192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d196192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150077, d196192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21260 q = 1) (hb : d116753 q = 1) : d196195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21260, d196195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46518 q ha hb
    | true =>
      simp only [d21260, d196195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46519 q ha hb
  have h16 (q : Pattern) (ha : d21261 q = 1) (hb : d116753 q = 1) : d196196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21261, d196196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21261, d196196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21262 q = 1) (hb : d116753 q = 1) : d196197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21262, d196197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21262, d196197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21263 q = 1) (hb : d116753 q = 1) : d196198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21263, d196198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21263, d196198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21266 q = 1) (hb : d116753 q = 1) : d196200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21266, d196200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46520 q ha hb
    | true =>
      simp only [d21266, d196200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46521 q ha hb
  have h20 (q : Pattern) (ha : d21267 q = 1) (hb : d116753 q = 1) : d196201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21267, d196201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21267, d196201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21268 q = 1) (hb : d116753 q = 1) : d196202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21268, d196202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21268, d196202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21270 q = 1) (hb : d116753 q = 1) : d196204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d196204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46522 q ha hb
    | true =>
      simp only [d21270, d196204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46500 q ha hb
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150079 q = 1) : d196205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d196205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150079, d196205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21276 q = 1) (hb : d116753 q = 1) : d196207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d196207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46523 q ha hb
    | true =>
      simp only [d21276, d196207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21277 q = 1) (hb : d116753 q = 1) : d196208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d196208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21277, d196208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116753 q = 1) (hb : d150080 q = 1) : d196209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d196209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150080, d196209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116753 q = 1) (hb : d150081 q = 1) : d196210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d196210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150081, d196210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116753 q = 1) (hb : d150082 q = 1) : d196211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d196211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150082, d196211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116753 q = 1) (hb : d150083 q = 1) : d196212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d196212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150083, d196212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro46525 (p : Pattern) (ha : d116753 p = 1) (hb : d150090 p = 1) : d196221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21270 q = 1) (hb : d116753 q = 1) : d196204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d196204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46522 q ha hb
    | true =>
      simp only [d21270, d196204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46500 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150079 q = 1) : d196205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d196205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150079, d196205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21276 q = 1) (hb : d116753 q = 1) : d196207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d196207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46523 q ha hb
    | true =>
      simp only [d21276, d196207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21277 q = 1) (hb : d116753 q = 1) : d196208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d196208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21277, d196208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150080 q = 1) : d196209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d196209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150080, d196209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150088 q = 1) : d196219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d196219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150088, d196219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150089 q = 1) : d196220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d196220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150089, d196220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150090 q = 1) : d196221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d196221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150090, d196221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46526 (p : Pattern) (ha : d21319 p = 1) (hb : d116752 p = 1) : d196227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21318 q = 1) (hb : d116750 q = 1) : d21318 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21319 q = 1) (hb : d116752 q = 1) : d196227 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21319, d116752, d196227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21319, d116752, d196227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46527 (p : Pattern) (ha : d21329 p = 1) (hb : d116753 p = 1) : d196233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21320 q = 1) (hb : d116752 q = 1) : d196228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21320, d196228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46526 q ha hb
    | true =>
      simp only [d21320, d196228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46488 q ha hb
  have h2 (q : Pattern) (ha : d21321 q = 1) (hb : d116752 q = 1) : d196229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21321, d196229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21321, d196229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21322 q = 1) (hb : d116752 q = 1) : d196230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21322, d196230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21322, d196230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21326 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21327 q = 1) (hb : d116753 q = 1) : d196231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21327, d116753, d196231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21327, d116753, d196231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21078 q = 1) (hb : d116752 q = 1) : d196112 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46488 q ha hb
    | true =>
      simp only [d21078, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46467 q ha hb
  have h7 (q : Pattern) (ha : d21079 q = 1) (hb : d116752 q = 1) : d196113 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21080 q = 1) (hb : d116752 q = 1) : d196114 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d20935 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21081 q = 1) (hb : d116753 q = 1) : d196115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d116753, d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21081, d116753, d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21328 q = 1) (hb : d116753 q = 1) : d196232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21328, d196232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21328, d196232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21329 q = 1) (hb : d116753 q = 1) : d196233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21329, d196233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21329, d196233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46528 (p : Pattern) (ha : d21334 p = 1) (hb : d116753 p = 1) : d196117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d116752 q = 1) : d196112 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46488 q ha hb
    | true =>
      simp only [d21078, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46467 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d116752 q = 1) : d196113 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d116752 q = 1) : d196114 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20935 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21081 q = 1) (hb : d116753 q = 1) : d196115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d116753, d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d116753, d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d20933 q = 1) (hb : d116752 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46467 q ha hb
    | true =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h7 (q : Pattern) (ha : d20934 q = 1) (hb : d116752 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20935 q = 1) (hb : d116752 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21332 q = 1) (hb : d116753 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21332, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21333 q = 1) (hb : d116753 q = 1) : d196116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21333, d196116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21333, d196116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21334 q = 1) (hb : d116753 q = 1) : d196117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21334, d196117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21334, d196117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46529 (p : Pattern) (ha : d21340 p = 1) (hb : d116753 p = 1) : d196239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21330 q = 1) (hb : d116753 q = 1) : d196234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21330, d196234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46527 q ha hb
    | true =>
      simp only [d21330, d196234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21331 q = 1) (hb : d116753 q = 1) : d196235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21331, d196235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21331, d196235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21335 q = 1) (hb : d116753 q = 1) : d196118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46528 q ha hb
    | true =>
      simp only [d21335, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21336 q = 1) (hb : d116753 q = 1) : d196119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21337 q = 1) (hb : d116753 q = 1) : d196236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21337, d196236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21337, d196236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21338 q = 1) (hb : d116753 q = 1) : d196237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21338, d196237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21338, d196237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21339 q = 1) (hb : d116753 q = 1) : d196238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21339, d196238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21339, d196238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21340 q = 1) (hb : d116753 q = 1) : d196239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21340, d196239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21340, d196239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46530 (p : Pattern) (ha : d21348 p = 1) (hb : d116753 p = 1) : d196123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d116753 q = 1) : d196118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46528 q ha hb
    | true =>
      simp only [d21335, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d116753 q = 1) : d196119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21343 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46506 q ha hb
    | true =>
      simp only [d21343, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21344 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21345 q = 1) (hb : d116753 q = 1) : d196120 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21345, d196120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21345, d196120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21346 q = 1) (hb : d116753 q = 1) : d196121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21346, d196121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21346, d196121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21347 q = 1) (hb : d116753 q = 1) : d196122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21347, d196122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21347, d196122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21348 q = 1) (hb : d116753 q = 1) : d196123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21348, d196123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21348, d196123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46531 (p : Pattern) (ha : d21387 p = 1) (hb : d116753 p = 1) : d196245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d116753 q = 1) : d196118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46528 q ha hb
    | true =>
      simp only [d21335, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d116753 q = 1) : d196119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21384 q = 1) (hb : d116753 q = 1) : d196242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21384, d196242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21384, d196242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21385 q = 1) (hb : d116753 q = 1) : d196243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21385, d196243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21385, d196243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21386 q = 1) (hb : d116753 q = 1) : d196244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21386, d196244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21386, d196244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21387 q = 1) (hb : d116753 q = 1) : d196245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21387, d196245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21387, d196245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46532 (p : Pattern) (ha : d116753 p = 1) (hb : d150100 p = 1) : d196251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21349 q = 1) (hb : d116753 q = 1) : d196240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21349, d196240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46529 q ha hb
    | true =>
      simp only [d21349, d196240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46530 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150096 q = 1) : d196241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d196241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150096, d196241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21388 q = 1) (hb : d116753 q = 1) : d196246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21388, d196246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46531 q ha hb
    | true =>
      simp only [d21388, d196246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21389 q = 1) (hb : d116753 q = 1) : d196247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21389, d196247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21389, d196247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150097 q = 1) : d196248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d196248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150097, d196248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150098 q = 1) : d196249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d196249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150098, d196249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150099 q = 1) : d196250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d196250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150099, d196250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150100 q = 1) : d196251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d196251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150100, d196251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46533 (p : Pattern) (ha : d116753 p = 1) (hb : d150106 p = 1) : d196257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21152 q = 1) (hb : d116753 q = 1) : d196147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21152, d196147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21152, d196147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46499 q ha hb
  have h2 (q : Pattern) (ha : d21153 q = 1) (hb : d116753 q = 1) : d196148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21153, d196148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21153, d196148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21162 q = 1) (hb : d116753 q = 1) : d196154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d196154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46499 q ha hb
    | true =>
      simp only [d21162, d196154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46502 q ha hb
  have h4 (q : Pattern) (ha : d21163 q = 1) (hb : d116753 q = 1) : d196155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d196155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21163, d196155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21164 q = 1) (hb : d116753 q = 1) : d196156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21164, d196156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21164, d196156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150084 q = 1) : d196213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d196213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46517 q ha hb
    | true =>
      simp only [d150084, d196213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46524 q ha hb
  have h7 (q : Pattern) (ha : d21295 q = 1) (hb : d116753 q = 1) : d196215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21295, d196215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46503 q ha hb
    | true =>
      simp only [d21295, d196215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46504 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150085 q = 1) : d196216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d196216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150085, d196216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150086 q = 1) : d196217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d196217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150086, d196217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150087 q = 1) : d196218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d196218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150087, d196218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150091 q = 1) : d196222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d196222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150091, d196222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46525 q ha hb
  have h12 (q : Pattern) (ha : d21304 q = 1) (hb : d116753 q = 1) : d120335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21304, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21304, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46505 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150092 q = 1) : d196223 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d196223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150092, d196223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150093 q = 1) : d196224 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d196224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150093, d196224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150094 q = 1) : d196225 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d196225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150094, d196225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150095 q = 1) : d196226 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d196226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150095, d196226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116753 q = 1) (hb : d150101 q = 1) : d196252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d196252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150101, d196252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46532 q ha hb
  have h18 (q : Pattern) (ha : d21405 q = 1) (hb : d116753 q = 1) : d120379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21405, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21405, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46508 q ha hb
  have h19 (q : Pattern) (ha : d116753 q = 1) (hb : d150102 q = 1) : d196253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d196253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150102, d196253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116753 q = 1) (hb : d150103 q = 1) : d196254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d196254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150103, d196254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116753 q = 1) (hb : d150104 q = 1) : d196255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d196255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150104, d196255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116753 q = 1) (hb : d150105 q = 1) : d196256 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d196256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150105, d196256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150106 q = 1) : d196257 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d196257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150106, d196257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46534 (p : Pattern) (ha : d116753 p = 1) (hb : d150112 p = 1) : d196263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150107 q = 1) : d196258 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d196258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150107, d196258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46533 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150108 q = 1) : d196259 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d196259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150108, d196259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150109 q = 1) : d196260 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d196260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150109, d196260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150110 q = 1) : d196261 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d196261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150110, d196261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150111 q = 1) : d196262 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d196262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150111, d196262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150112 q = 1) : d196263 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d196263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150112, d196263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46535 (p : Pattern) (ha : d21419 p = 1) (hb : d116752 p = 1) : d196265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21187 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21418 q = 1) (hb : d116750 q = 1) : d21418 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21419 q = 1) (hb : d116752 q = 1) : d196265 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21419, d116752, d196265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21419, d116752, d196265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46536 (p : Pattern) (ha : d21420 p = 1) (hb : d116752 p = 1) : d120392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20994 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d757 q = 1) (hb : d116750 q = 1) : d757 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21420 q = 1) (hb : d116752 q = 1) : d120392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21420, d116752, d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21420, d116752, d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46537 (p : Pattern) (ha : d21430 p = 1) (hb : d116753 p = 1) : d196271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21421 q = 1) (hb : d116752 q = 1) : d196266 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46535 q ha hb
    | true =>
      simp only [d21421, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46536 q ha hb
  have h2 (q : Pattern) (ha : d21422 q = 1) (hb : d116752 q = 1) : d196267 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21423 q = 1) (hb : d116752 q = 1) : d196268 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21426 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21427 q = 1) (hb : d116753 q = 1) : d196269 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d116753, d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21427, d116753, d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21424 q = 1) (hb : d116752 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46536 q ha hb
    | true =>
      simp only [d21424, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19864 q ha hb
  have h7 (q : Pattern) (ha : d21425 q = 1) (hb : d116752 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21426 q = 1) (hb : d116752 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21428 q = 1) (hb : d116753 q = 1) : d120400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21428, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21429 q = 1) (hb : d116753 q = 1) : d196270 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21429, d196270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21429, d196270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21430 q = 1) (hb : d116753 q = 1) : d196271 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21430, d196271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21430, d196271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46538 (p : Pattern) (ha : d21434 p = 1) (hb : d116753 p = 1) : d120406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21424 q = 1) (hb : d116752 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46536 q ha hb
    | true =>
      simp only [d21424, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19864 q ha hb
  have h2 (q : Pattern) (ha : d21425 q = 1) (hb : d116752 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21426 q = 1) (hb : d116752 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21428 q = 1) (hb : d116753 q = 1) : d120400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21428, d116753, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21433 q = 1) (hb : d116753 q = 1) : d120405 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21433, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21433, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21434 q = 1) (hb : d116753 q = 1) : d120406 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21434, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21434, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46539 (p : Pattern) (ha : d21440 p = 1) (hb : d116753 p = 1) : d196277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d116753 q = 1) : d196274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d116753 q = 1) : d196275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d116753 q = 1) : d196276 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d196276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d196276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21440 q = 1) (hb : d116753 q = 1) : d196277 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21440, d196277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21440, d196277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46540 (p : Pattern) (ha : d21444 p = 1) (hb : d116753 p = 1) : d120416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d116753 q = 1) : d120415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21444 q = 1) (hb : d116753 q = 1) : d120416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21444, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21444, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46541 (p : Pattern) (ha : d21450 p = 1) (hb : d116753 p = 1) : d196283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d116753 q = 1) : d196278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d196278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46539 q ha hb
    | true =>
      simp only [d21445, d196278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46540 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d116753 q = 1) : d196279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d196279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d196279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d116753 q = 1) : d196280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d196280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d196280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d116753 q = 1) : d196281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d196281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d196281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d116753 q = 1) : d196282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d196282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d196282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21450 q = 1) (hb : d116753 q = 1) : d196283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d196283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d196283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46542 (p : Pattern) (ha : d21453 p = 1) (hb : d116753 p = 1) : d196286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d116753 q = 1) : d196274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d116753 q = 1) : d196275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d116753 q = 1) : d196276 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d196276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d196276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21453 q = 1) (hb : d116753 q = 1) : d196286 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21453, d196286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21453, d196286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46543 (p : Pattern) (ha : d21454 p = 1) (hb : d116753 p = 1) : d120426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d116753 q = 1) : d120415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21454 q = 1) (hb : d116753 q = 1) : d120426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21454, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21454, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46544 (p : Pattern) (ha : d21460 p = 1) (hb : d116753 p = 1) : d196292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d116753 q = 1) : d196278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d196278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46539 q ha hb
    | true =>
      simp only [d21445, d196278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46540 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d116753 q = 1) : d196279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d196279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d196279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d116753 q = 1) : d196280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d196280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d196280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d116753 q = 1) : d196281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d196281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d196281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d116753 q = 1) : d196282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d196282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d196282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21455 q = 1) (hb : d116753 q = 1) : d196287 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d196287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46542 q ha hb
    | true =>
      simp only [d21455, d196287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46543 q ha hb
  have h7 (q : Pattern) (ha : d21456 q = 1) (hb : d116753 q = 1) : d196288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d196288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d196288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21457 q = 1) (hb : d116753 q = 1) : d196289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d196289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21457, d196289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21458 q = 1) (hb : d116753 q = 1) : d196290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d196290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d196290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21459 q = 1) (hb : d116753 q = 1) : d196291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d196291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d196291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21460 q = 1) (hb : d116753 q = 1) : d196292 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d196292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21460, d196292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46545 (p : Pattern) (ha : d21591 p = 1) (hb : d116753 p = 1) : d196353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d116753 q = 1) : d196278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d196278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46539 q ha hb
    | true =>
      simp only [d21445, d196278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46540 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d116753 q = 1) : d196279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d196279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d196279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d116753 q = 1) : d196280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d196280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d196280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d116753 q = 1) : d196281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d196281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d196281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d116753 q = 1) : d196282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d196282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d196282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21586 q = 1) (hb : d116753 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46540 q ha hb
    | true =>
      simp only [d21586, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21587 q = 1) (hb : d116753 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21588 q = 1) (hb : d116753 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21588, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21589 q = 1) (hb : d116753 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21590 q = 1) (hb : d116753 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21591 q = 1) (hb : d116753 q = 1) : d196353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21591, d196353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21591, d196353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46546 (p : Pattern) (ha : d21597 p = 1) (hb : d116753 p = 1) : d120525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21586 q = 1) (hb : d116753 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46540 q ha hb
    | true =>
      simp only [d21586, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21587 q = 1) (hb : d116753 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21588 q = 1) (hb : d116753 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21588, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21589 q = 1) (hb : d116753 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21590 q = 1) (hb : d116753 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21592 q = 1) (hb : d116753 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46543 q ha hb
    | true =>
      simp only [d21592, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21593 q = 1) (hb : d116753 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21594 q = 1) (hb : d116753 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21594, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21595 q = 1) (hb : d116753 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21596 q = 1) (hb : d116753 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21597 q = 1) (hb : d116753 q = 1) : d120525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21597, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21597, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46547 (p : Pattern) (ha : d21606 p = 1) (hb : d116753 p = 1) : d120534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21592 q = 1) (hb : d116753 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46543 q ha hb
    | true =>
      simp only [d21592, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21593 q = 1) (hb : d116753 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21594 q = 1) (hb : d116753 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21594, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21595 q = 1) (hb : d116753 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21596 q = 1) (hb : d116753 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21606 q = 1) (hb : d116753 q = 1) : d120534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21606, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21606, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46548 (p : Pattern) (ha : d21633 p = 1) (hb : d116752 p = 1) : d120545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d980 q = 1) (hb : d116750 q = 1) : d980 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21633 q = 1) (hb : d116752 q = 1) : d120545 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21633, d116752, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21633, d116752, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46549 (p : Pattern) (ha : d21655 p = 1) (hb : d116753 p = 1) : d120567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21637 q = 1) (hb : d116752 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46548 q ha hb
    | true =>
      simp only [d21637, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19871 q ha hb
  have h2 (q : Pattern) (ha : d21638 q = 1) (hb : d116752 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21639 q = 1) (hb : d116752 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21645 q = 1) (hb : d116753 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21645, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21654 q = 1) (hb : d116753 q = 1) : d120566 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21654, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21654, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21655 q = 1) (hb : d116753 q = 1) : d120567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21655, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21655, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46550 (p : Pattern) (ha : d21715 p = 1) (hb : d116753 p = 1) : d120594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21656 q = 1) (hb : d116753 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46549 q ha hb
    | true =>
      simp only [d21656, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21657 q = 1) (hb : d116753 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21712 q = 1) (hb : d116753 q = 1) : d120591 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21712, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21712, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21713 q = 1) (hb : d116753 q = 1) : d120592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21713, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21713, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21714 q = 1) (hb : d116753 q = 1) : d120593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21714, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21714, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21715 q = 1) (hb : d116753 q = 1) : d120594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21715, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21715, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46551 (p : Pattern) (ha : d21721 p = 1) (hb : d116753 p = 1) : d120600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21716 q = 1) (hb : d116753 q = 1) : d120595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21716, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46550 q ha hb
    | true =>
      simp only [d21716, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21717 q = 1) (hb : d116753 q = 1) : d120596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21717, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21717, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21718 q = 1) (hb : d116753 q = 1) : d120597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21718, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21718, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21719 q = 1) (hb : d116753 q = 1) : d120598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21719, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21719, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21720 q = 1) (hb : d116753 q = 1) : d120599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21720, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21720, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21721 q = 1) (hb : d116753 q = 1) : d120600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21721, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21721, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46552 (p : Pattern) (ha : d21465 p = 1) (hb : d116753 p = 1) : d196297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d116753 q = 1) : d196274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d116753 q = 1) : d196275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d116753 q = 1) : d196296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d196296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d196296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21465 q = 1) (hb : d116753 q = 1) : d196297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21465, d196297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21465, d196297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46553 (p : Pattern) (ha : d21467 p = 1) (hb : d116753 p = 1) : d120439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d116753 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21467 q = 1) (hb : d116753 q = 1) : d120439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21467, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21467, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46554 (p : Pattern) (ha : d21474 p = 1) (hb : d116753 p = 1) : d196304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d116753 q = 1) : d196274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d116753 q = 1) : d196302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d196302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d196302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d116753 q = 1) : d196303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d196303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d196303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21474 q = 1) (hb : d116753 q = 1) : d196304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21474, d196304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21474, d196304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46555 (p : Pattern) (ha : d21477 p = 1) (hb : d116753 p = 1) : d120449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d116753 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d116753 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21477 q = 1) (hb : d116753 q = 1) : d120449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21477, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21477, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46556 (p : Pattern) (ha : d21493 p = 1) (hb : d116752 p = 1) : d196308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21492 q = 1) (hb : d116750 q = 1) : d21492 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21493 q = 1) (hb : d116752 q = 1) : d196308 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21493, d116752, d196308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21493, d116752, d196308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46557 (p : Pattern) (ha : d21503 p = 1) (hb : d116753 p = 1) : d196314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21494 q = 1) (hb : d116752 q = 1) : d196309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21494, d196309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46556 q ha hb
    | true =>
      simp only [d21494, d196309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46535 q ha hb
  have h2 (q : Pattern) (ha : d21495 q = 1) (hb : d116752 q = 1) : d196310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21495, d196310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21495, d196310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21496 q = 1) (hb : d116752 q = 1) : d196311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21496, d196311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21496, d196311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21500 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21501 q = 1) (hb : d116753 q = 1) : d196312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21501, d116753, d196312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21501, d116753, d196312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21421 q = 1) (hb : d116752 q = 1) : d196266 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46535 q ha hb
    | true =>
      simp only [d21421, d196266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46536 q ha hb
  have h7 (q : Pattern) (ha : d21422 q = 1) (hb : d116752 q = 1) : d196267 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d196267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21423 q = 1) (hb : d116752 q = 1) : d196268 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d196268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21426 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21427 q = 1) (hb : d116753 q = 1) : d196269 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d116753, d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21427, d116753, d196269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21502 q = 1) (hb : d116753 q = 1) : d196313 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21502, d196313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21502, d196313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21503 q = 1) (hb : d116753 q = 1) : d196314 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21503, d196314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21503, d196314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46558 (p : Pattern) (ha : d21509 p = 1) (hb : d116753 p = 1) : d196320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d116753 q = 1) : d196315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46557 q ha hb
    | true =>
      simp only [d21504, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d116753 q = 1) : d196316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d116753 q = 1) : d196317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d196317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d196317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d116753 q = 1) : d196318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d196318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d196318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d116753 q = 1) : d196319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d196319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d196319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21509 q = 1) (hb : d116753 q = 1) : d196320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21509, d196320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21509, d196320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46559 (p : Pattern) (ha : d21554 p = 1) (hb : d116753 p = 1) : d196326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d116753 q = 1) : d196323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d196323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d196323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d116753 q = 1) : d196324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d196324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d196324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d116753 q = 1) : d196325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d196325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d196325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21554 q = 1) (hb : d116753 q = 1) : d196326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21554, d196326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21554, d196326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46560 (p : Pattern) (ha : d116753 p = 1) (hb : d150118 p = 1) : d196332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d116753 q = 1) : d196298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d196298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46552 q ha hb
    | true =>
      simp only [d21468, d196298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46553 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d116753 q = 1) : d196299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d196299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d196299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d116753 q = 1) : d196300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d196300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d196300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d116753 q = 1) : d196301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d196301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d196301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d116753 q = 1) : d196305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d196305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46554 q ha hb
    | true =>
      simp only [d21478, d196305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46555 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d116753 q = 1) : d196306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d196306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d196306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d116753 q = 1) : d196307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d196307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d196307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d116753 q = 1) : d196321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d196321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46558 q ha hb
    | true =>
      simp only [d21510, d196321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46539 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150114 q = 1) : d196322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d196322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150114, d196322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d116753 q = 1) : d196327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d196327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46559 q ha hb
    | true =>
      simp only [d21555, d196327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d116753 q = 1) : d196328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d196328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d196328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150115 q = 1) : d196329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d196329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d196329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150116 q = 1) : d196330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d196330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150116, d196330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150117 q = 1) : d196331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d196331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150117, d196331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150118 q = 1) : d196332 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d196332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150118, d196332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46561 (p : Pattern) (ha : d21561 p = 1) (hb : d116753 p = 1) : d196333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d116753 q = 1) : d196274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d116753 q = 1) : d196275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d196275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d116753 q = 1) : d196296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d196296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d196296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21561 q = 1) (hb : d116753 q = 1) : d196333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21561, d196333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21561, d196333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46562 (p : Pattern) (ha : d21562 p = 1) (hb : d116753 p = 1) : d120487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d116753 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d116753 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21562 q = 1) (hb : d116753 q = 1) : d120487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21562, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21562, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46563 (p : Pattern) (ha : d21567 p = 1) (hb : d116753 p = 1) : d196338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d116753 q = 1) : d196274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d196274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d116753 q = 1) : d196302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d196302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d196302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d116753 q = 1) : d196303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d196303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d196303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21567 q = 1) (hb : d116753 q = 1) : d196338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21567, d196338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21567, d196338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46564 (p : Pattern) (ha : d21568 p = 1) (hb : d116753 p = 1) : d120493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d116753 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46538 q ha hb
    | true =>
      simp only [d21435, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d116753 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d116753 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d116753 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d116753 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21568 q = 1) (hb : d116753 q = 1) : d120493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21568, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21568, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46565 (p : Pattern) (ha : d21572 p = 1) (hb : d116753 p = 1) : d196342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d116753 q = 1) : d196315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46557 q ha hb
    | true =>
      simp only [d21504, d196315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d116753 q = 1) : d196316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d196316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d116753 q = 1) : d196317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d196317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d196317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d116753 q = 1) : d196318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d196318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d196318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d116753 q = 1) : d196319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d196319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d196319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21572 q = 1) (hb : d116753 q = 1) : d196342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21572, d196342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21572, d196342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46566 (p : Pattern) (ha : d21578 p = 1) (hb : d116753 p = 1) : d196345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d116753 q = 1) : d196272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46537 q ha hb
    | true =>
      simp only [d21431, d196272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d116753 q = 1) : d196273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d196273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d116753 q = 1) : d196323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d196323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d196323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d116753 q = 1) : d196324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d196324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d196324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d116753 q = 1) : d196325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d196325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d196325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21578 q = 1) (hb : d116753 q = 1) : d196345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21578, d196345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21578, d196345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46567 (p : Pattern) (ha : d116753 p = 1) (hb : d150123 p = 1) : d196351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d116753 q = 1) : d196298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d196298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46552 q ha hb
    | true =>
      simp only [d21468, d196298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46553 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d116753 q = 1) : d196299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d196299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d196299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d116753 q = 1) : d196300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d196300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d196300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d116753 q = 1) : d196301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d196301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d196301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d116753 q = 1) : d196305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d196305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46554 q ha hb
    | true =>
      simp only [d21478, d196305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46555 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d116753 q = 1) : d196306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d196306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d196306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d116753 q = 1) : d196307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d196307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d196307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d116753 q = 1) : d196321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d196321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46558 q ha hb
    | true =>
      simp only [d21510, d196321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46539 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150114 q = 1) : d196322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d196322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150114, d196322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d116753 q = 1) : d196327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d196327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46559 q ha hb
    | true =>
      simp only [d21555, d196327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d116753 q = 1) : d196328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d196328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d196328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150115 q = 1) : d196329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d196329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d196329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150116 q = 1) : d196330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d196330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150116, d196330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150117 q = 1) : d196331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d196331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150117, d196331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21563 q = 1) (hb : d116753 q = 1) : d196334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21563, d196334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46561 q ha hb
    | true =>
      simp only [d21563, d196334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46562 q ha hb
  have h16 (q : Pattern) (ha : d21564 q = 1) (hb : d116753 q = 1) : d196335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21564, d196335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21564, d196335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21565 q = 1) (hb : d116753 q = 1) : d196336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21565, d196336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21565, d196336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21566 q = 1) (hb : d116753 q = 1) : d196337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21566, d196337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21566, d196337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21569 q = 1) (hb : d116753 q = 1) : d196339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21569, d196339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46563 q ha hb
    | true =>
      simp only [d21569, d196339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46564 q ha hb
  have h20 (q : Pattern) (ha : d21570 q = 1) (hb : d116753 q = 1) : d196340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21570, d196340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21570, d196340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21571 q = 1) (hb : d116753 q = 1) : d196341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21571, d196341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21571, d196341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21573 q = 1) (hb : d116753 q = 1) : d196343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d196343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46565 q ha hb
    | true =>
      simp only [d21573, d196343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46542 q ha hb
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150119 q = 1) : d196344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d196344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150119, d196344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21579 q = 1) (hb : d116753 q = 1) : d196346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d196346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46566 q ha hb
    | true =>
      simp only [d21579, d196346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21580 q = 1) (hb : d116753 q = 1) : d196347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d196347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21580, d196347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116753 q = 1) (hb : d150120 q = 1) : d196348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d196348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150120, d196348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116753 q = 1) (hb : d150121 q = 1) : d196349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d196349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150121, d196349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116753 q = 1) (hb : d150122 q = 1) : d196350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d196350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150122, d196350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116753 q = 1) (hb : d150123 q = 1) : d196351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d196351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150123, d196351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro46568 (p : Pattern) (ha : d116753 p = 1) (hb : d150130 p = 1) : d196360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21573 q = 1) (hb : d116753 q = 1) : d196343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d196343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46565 q ha hb
    | true =>
      simp only [d21573, d196343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46542 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150119 q = 1) : d196344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d196344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150119, d196344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21579 q = 1) (hb : d116753 q = 1) : d196346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d196346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46566 q ha hb
    | true =>
      simp only [d21579, d196346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21580 q = 1) (hb : d116753 q = 1) : d196347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d196347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21580, d196347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150120 q = 1) : d196348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d196348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150120, d196348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150128 q = 1) : d196358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d196358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150128, d196358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150129 q = 1) : d196359 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d196359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150129, d196359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150130 q = 1) : d196360 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d196360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150130, d196360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46569 (p : Pattern) (ha : d21622 p = 1) (hb : d116752 p = 1) : d196366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21616 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21621 q = 1) (hb : d116750 q = 1) : d21621 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21622 q = 1) (hb : d116752 q = 1) : d196366 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21622, d116752, d196366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21622, d116752, d196366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46570 (p : Pattern) (ha : d21624 p = 1) (hb : d116752 p = 1) : d196367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21623 q = 1) (hb : d116750 q = 1) : d21623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21624 q = 1) (hb : d116752 q = 1) : d196367 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21624, d116752, d196367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21624, d116752, d196367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46571 (p : Pattern) (ha : d21642 p = 1) (hb : d116753 p = 1) : d196377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21625 q = 1) (hb : d116752 q = 1) : d196368 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21625, d196368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46569 q ha hb
    | true =>
      simp only [d21625, d196368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46570 q ha hb
  have h2 (q : Pattern) (ha : d21626 q = 1) (hb : d116752 q = 1) : d196369 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21626, d196369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21626, d196369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21627 q = 1) (hb : d116752 q = 1) : d196370 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21627, d196370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21627, d196370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21631 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21632 q = 1) (hb : d116753 q = 1) : d196371 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21632, d116753, d196371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21632, d116753, d196371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21634 q = 1) (hb : d116752 q = 1) : d196372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46570 q ha hb
    | true =>
      simp only [d21634, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46548 q ha hb
  have h7 (q : Pattern) (ha : d21635 q = 1) (hb : d116752 q = 1) : d196373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21636 q = 1) (hb : d116752 q = 1) : d196374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21640 q = 1) (hb : d116753 q = 1) : d196375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d116753, d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21640, d116753, d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21641 q = 1) (hb : d116753 q = 1) : d196376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21641, d196376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21641, d196376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21642 q = 1) (hb : d116753 q = 1) : d196377 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21642, d196377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21642, d196377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46572 (p : Pattern) (ha : d21647 p = 1) (hb : d116753 p = 1) : d196381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21634 q = 1) (hb : d116752 q = 1) : d196372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46570 q ha hb
    | true =>
      simp only [d21634, d196372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46548 q ha hb
  have h2 (q : Pattern) (ha : d21635 q = 1) (hb : d116752 q = 1) : d196373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d196373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21636 q = 1) (hb : d116752 q = 1) : d196374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d196374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21639 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21640 q = 1) (hb : d116753 q = 1) : d196375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d116753, d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21640, d116753, d196375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21637 q = 1) (hb : d116752 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46548 q ha hb
    | true =>
      simp only [d21637, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19871 q ha hb
  have h7 (q : Pattern) (ha : d21638 q = 1) (hb : d116752 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21639 q = 1) (hb : d116752 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21645 q = 1) (hb : d116753 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21645, d116753, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21646 q = 1) (hb : d116753 q = 1) : d196380 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21646, d196380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21646, d196380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21647 q = 1) (hb : d116753 q = 1) : d196381 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21647, d196381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21647, d196381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46573 (p : Pattern) (ha : d21653 p = 1) (hb : d116753 p = 1) : d196387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21643 q = 1) (hb : d116753 q = 1) : d196378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21643, d196378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46571 q ha hb
    | true =>
      simp only [d21643, d196378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21644 q = 1) (hb : d116753 q = 1) : d196379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21644, d196379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21644, d196379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21648 q = 1) (hb : d116753 q = 1) : d196382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d196382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46572 q ha hb
    | true =>
      simp only [d21648, d196382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21649 q = 1) (hb : d116753 q = 1) : d196383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d196383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d196383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21650 q = 1) (hb : d116753 q = 1) : d196384 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21650, d196384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21650, d196384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21651 q = 1) (hb : d116753 q = 1) : d196385 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21651, d196385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21651, d196385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21652 q = 1) (hb : d116753 q = 1) : d196386 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21652, d196386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21652, d196386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21653 q = 1) (hb : d116753 q = 1) : d196387 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21653, d196387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21653, d196387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46574 (p : Pattern) (ha : d21661 p = 1) (hb : d116753 p = 1) : d196391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d116753 q = 1) : d196382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d196382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46572 q ha hb
    | true =>
      simp only [d21648, d196382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d116753 q = 1) : d196383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d196383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d196383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21656 q = 1) (hb : d116753 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46549 q ha hb
    | true =>
      simp only [d21656, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21657 q = 1) (hb : d116753 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21658 q = 1) (hb : d116753 q = 1) : d196388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21658, d196388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21658, d196388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21659 q = 1) (hb : d116753 q = 1) : d196389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21659, d196389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21659, d196389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21660 q = 1) (hb : d116753 q = 1) : d196390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21660, d196390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21660, d196390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21661 q = 1) (hb : d116753 q = 1) : d196391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21661, d196391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21661, d196391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46575 (p : Pattern) (ha : d21704 p = 1) (hb : d116753 p = 1) : d196397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d116753 q = 1) : d196382 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d196382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46572 q ha hb
    | true =>
      simp only [d21648, d196382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d116753 q = 1) : d196383 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d196383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d196383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21701 q = 1) (hb : d116753 q = 1) : d196394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21701, d196394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21701, d196394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21702 q = 1) (hb : d116753 q = 1) : d196395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21702, d196395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21702, d196395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21703 q = 1) (hb : d116753 q = 1) : d196396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21703, d196396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21703, d196396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21704 q = 1) (hb : d116753 q = 1) : d196397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21704, d196397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21704, d196397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46576 (p : Pattern) (ha : d116753 p = 1) (hb : d150140 p = 1) : d196403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21662 q = 1) (hb : d116753 q = 1) : d196392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21662, d196392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46573 q ha hb
    | true =>
      simp only [d21662, d196392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46574 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150136 q = 1) : d196393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d196393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150136, d196393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21705 q = 1) (hb : d116753 q = 1) : d196398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21705, d196398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46575 q ha hb
    | true =>
      simp only [d21705, d196398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21706 q = 1) (hb : d116753 q = 1) : d196399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21706, d196399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21706, d196399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150137 q = 1) : d196400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d196400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150137, d196400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150138 q = 1) : d196401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d196401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150138, d196401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150139 q = 1) : d196402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d196402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150139, d196402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150140 q = 1) : d196403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d196403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150140, d196403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46577 (p : Pattern) (ha : d116753 p = 1) (hb : d150146 p = 1) : d196409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21451 q = 1) (hb : d116753 q = 1) : d196284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21451, d196284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21451, d196284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46541 q ha hb
  have h2 (q : Pattern) (ha : d21452 q = 1) (hb : d116753 q = 1) : d196285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21452, d196285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21452, d196285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21461 q = 1) (hb : d116753 q = 1) : d196293 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d196293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46541 q ha hb
    | true =>
      simp only [d21461, d196293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46544 q ha hb
  have h4 (q : Pattern) (ha : d21462 q = 1) (hb : d116753 q = 1) : d196294 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d196294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21462, d196294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21463 q = 1) (hb : d116753 q = 1) : d196295 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21463, d196295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21463, d196295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150124 q = 1) : d196352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d196352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46560 q ha hb
    | true =>
      simp only [d150124, d196352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46567 q ha hb
  have h7 (q : Pattern) (ha : d21598 q = 1) (hb : d116753 q = 1) : d196354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21598, d196354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46545 q ha hb
    | true =>
      simp only [d21598, d196354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46546 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150125 q = 1) : d196355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d196355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150125, d196355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150126 q = 1) : d196356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d196356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150126, d196356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150127 q = 1) : d196357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d196357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150127, d196357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150131 q = 1) : d196361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d196361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150131, d196361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46568 q ha hb
  have h12 (q : Pattern) (ha : d21607 q = 1) (hb : d116753 q = 1) : d120535 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21607, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21607, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46547 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150132 q = 1) : d196362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d196362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150132, d196362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150133 q = 1) : d196363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d196363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150133, d196363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150134 q = 1) : d196364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d196364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150134, d196364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150135 q = 1) : d196365 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d196365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150135, d196365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116753 q = 1) (hb : d150141 q = 1) : d196404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d196404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150141, d196404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46576 q ha hb
  have h18 (q : Pattern) (ha : d21722 q = 1) (hb : d116753 q = 1) : d120601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21722, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21722, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46551 q ha hb
  have h19 (q : Pattern) (ha : d116753 q = 1) (hb : d150142 q = 1) : d196405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d196405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150142, d196405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116753 q = 1) (hb : d150143 q = 1) : d196406 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d196406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150143, d196406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116753 q = 1) (hb : d150144 q = 1) : d196407 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d196407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150144, d196407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116753 q = 1) (hb : d150145 q = 1) : d196408 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d196408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150145, d196408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150146 q = 1) : d196409 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d196409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150146, d196409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46578 (p : Pattern) (ha : d116753 p = 1) (hb : d150152 p = 1) : d196415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150147 q = 1) : d196410 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d196410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150147, d196410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46577 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150148 q = 1) : d196411 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d196411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150148, d196411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150149 q = 1) : d196412 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d196412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150149, d196412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150150 q = 1) : d196413 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d196413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150150, d196413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150151 q = 1) : d196414 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d196414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150151, d196414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150152 q = 1) : d196415 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d196415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150152, d196415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46579 (p : Pattern) (ha : d21753 p = 1) (hb : d116752 p = 1) : d196418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21746 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21752 q = 1) (hb : d116750 q = 1) : d21752 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21753 q = 1) (hb : d116752 q = 1) : d196418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21753, d116752, d196418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21753, d116752, d196418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46580 (p : Pattern) (ha : d21761 p = 1) (hb : d116752 p = 1) : d196419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21759 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21760 q = 1) (hb : d116750 q = 1) : d21760 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21761 q = 1) (hb : d116752 q = 1) : d196419 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21761, d116752, d196419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21761, d116752, d196419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46581 (p : Pattern) (ha : d21777 p = 1) (hb : d116752 p = 1) : d196424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14772 q = 1) (hb : d116750 q = 1) : d14772 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21777 q = 1) (hb : d116752 q = 1) : d196424 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21777, d116752, d196424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21777, d116752, d196424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46582 (p : Pattern) (ha : d21783 p = 1) (hb : d116753 p = 1) : d196430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d116752 q = 1) : d196420 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46579 q ha hb
    | true =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d116752 q = 1) : d196421 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d116752 q = 1) : d196422 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21775 q = 1) (hb : d116753 q = 1) : d196423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21778 q = 1) (hb : d116752 q = 1) : d196425 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d196425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
    | true =>
      simp only [d21778, d196425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46581 q ha hb
  have h7 (q : Pattern) (ha : d21779 q = 1) (hb : d116752 q = 1) : d196426 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d196426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d196426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21780 q = 1) (hb : d116752 q = 1) : d196427 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d196427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d196427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21781 q = 1) (hb : d116753 q = 1) : d196428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d116753, d196428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21781, d116753, d196428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21782 q = 1) (hb : d116753 q = 1) : d196429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21782, d196429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21782, d196429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21783 q = 1) (hb : d116753 q = 1) : d196430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21783, d196430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21783, d196430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46583 (p : Pattern) (ha : d21787 p = 1) (hb : d116753 p = 1) : d196434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21778 q = 1) (hb : d116752 q = 1) : d196425 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d196425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
    | true =>
      simp only [d21778, d196425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46581 q ha hb
  have h2 (q : Pattern) (ha : d21779 q = 1) (hb : d116752 q = 1) : d196426 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d196426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d196426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21780 q = 1) (hb : d116752 q = 1) : d196427 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d196427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d196427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21781 q = 1) (hb : d116753 q = 1) : d196428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d116753, d196428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21781, d116753, d196428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21786 q = 1) (hb : d116753 q = 1) : d196433 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21786, d196433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21786, d196433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21787 q = 1) (hb : d116753 q = 1) : d196434 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21787, d196434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21787, d196434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46584 (p : Pattern) (ha : d21793 p = 1) (hb : d116753 p = 1) : d196440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46582 q ha hb
    | true =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d116753 q = 1) : d196438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d116753 q = 1) : d196439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21793 q = 1) (hb : d116753 q = 1) : d196440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21793, d196440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21793, d196440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46585 (p : Pattern) (ha : d21797 p = 1) (hb : d116753 p = 1) : d196444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d116753 q = 1) : d196441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d116753 q = 1) : d196442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d116753 q = 1) : d196443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d196443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d196443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21797 q = 1) (hb : d116753 q = 1) : d196444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21797, d196444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21797, d196444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46586 (p : Pattern) (ha : d21803 p = 1) (hb : d116753 p = 1) : d196450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d116753 q = 1) : d196445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d196445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46584 q ha hb
    | true =>
      simp only [d21798, d196445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46585 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d116753 q = 1) : d196446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d196446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d196446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d116753 q = 1) : d196447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d196447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d196447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d116753 q = 1) : d196448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d196448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d196448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d116753 q = 1) : d196449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d196449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d196449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21803 q = 1) (hb : d116753 q = 1) : d196450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d196450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d196450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46587 (p : Pattern) (ha : d21806 p = 1) (hb : d116753 p = 1) : d196453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46582 q ha hb
    | true =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d116753 q = 1) : d196438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d116753 q = 1) : d196439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21806 q = 1) (hb : d116753 q = 1) : d196453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21806, d196453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21806, d196453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46588 (p : Pattern) (ha : d21807 p = 1) (hb : d116753 p = 1) : d196454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d116753 q = 1) : d196441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d116753 q = 1) : d196442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d116753 q = 1) : d196443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d196443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d196443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21807 q = 1) (hb : d116753 q = 1) : d196454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21807, d196454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21807, d196454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46589 (p : Pattern) (ha : d21813 p = 1) (hb : d116753 p = 1) : d196460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d116753 q = 1) : d196445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d196445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46584 q ha hb
    | true =>
      simp only [d21798, d196445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46585 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d116753 q = 1) : d196446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d196446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d196446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d116753 q = 1) : d196447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d196447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d196447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d116753 q = 1) : d196448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d196448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d196448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d116753 q = 1) : d196449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d196449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d196449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21808 q = 1) (hb : d116753 q = 1) : d196455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d196455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46587 q ha hb
    | true =>
      simp only [d21808, d196455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46588 q ha hb
  have h7 (q : Pattern) (ha : d21809 q = 1) (hb : d116753 q = 1) : d196456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d196456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d196456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21810 q = 1) (hb : d116753 q = 1) : d196457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d196457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21810, d196457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21811 q = 1) (hb : d116753 q = 1) : d196458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d196458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d196458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21812 q = 1) (hb : d116753 q = 1) : d196459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d196459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d196459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21813 q = 1) (hb : d116753 q = 1) : d196460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d196460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21813, d196460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46590 (p : Pattern) (ha : d21771 p = 1) (hb : d116752 p = 1) : d196424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14772 q = 1) (hb : d116750 q = 1) : d14772 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21771 q = 1) (hb : d116752 q = 1) : d196424 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21771, d116752, d196424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21771, d116752, d196424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46591 (p : Pattern) (ha : d21867 p = 1) (hb : d116753 p = 1) : d196430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d116752 q = 1) : d196420 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46579 q ha hb
    | true =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d116752 q = 1) : d196421 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d116752 q = 1) : d196422 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21775 q = 1) (hb : d116753 q = 1) : d196423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21772 q = 1) (hb : d116752 q = 1) : d196425 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d196425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
    | true =>
      simp only [d21772, d196425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46590 q ha hb
  have h7 (q : Pattern) (ha : d21773 q = 1) (hb : d116752 q = 1) : d196426 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d196426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d196426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21774 q = 1) (hb : d116752 q = 1) : d196427 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d196427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d196427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21865 q = 1) (hb : d116753 q = 1) : d196428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21865, d116753, d196428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21865, d116753, d196428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21866 q = 1) (hb : d116753 q = 1) : d196429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21866, d196429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21866, d196429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21867 q = 1) (hb : d116753 q = 1) : d196430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21867, d196430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21867, d196430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46592 (p : Pattern) (ha : d21877 p = 1) (hb : d116753 p = 1) : d196440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46591 q ha hb
    | true =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d116753 q = 1) : d196438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d116753 q = 1) : d196439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21877 q = 1) (hb : d116753 q = 1) : d196440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21877, d196440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21877, d196440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46593 (p : Pattern) (ha : d22003 p = 1) (hb : d116753 p = 1) : d196541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21993 q = 1) (hb : d116753 q = 1) : d196445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21993, d196445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46592 q ha hb
    | true =>
      simp only [d21993, d196445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46585 q ha hb
  have h2 (q : Pattern) (ha : d21994 q = 1) (hb : d116753 q = 1) : d196446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21994, d196446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21994, d196446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21995 q = 1) (hb : d116753 q = 1) : d196447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21995, d196447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21995, d196447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21996 q = 1) (hb : d116753 q = 1) : d196448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21996, d196448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21996, d196448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21997 q = 1) (hb : d116753 q = 1) : d196449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21997, d196449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21997, d196449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21998 q = 1) (hb : d116753 q = 1) : d196536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d196536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46585 q ha hb
    | true =>
      simp only [d21998, d196536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21999 q = 1) (hb : d116753 q = 1) : d196537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d196537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d196537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22000 q = 1) (hb : d116753 q = 1) : d196538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d196538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22000, d196538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22001 q = 1) (hb : d116753 q = 1) : d196539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d196539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d196539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22002 q = 1) (hb : d116753 q = 1) : d196540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d196540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d196540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22003 q = 1) (hb : d116753 q = 1) : d196541 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22003, d196541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22003, d196541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46594 (p : Pattern) (ha : d22009 p = 1) (hb : d116753 p = 1) : d196547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21998 q = 1) (hb : d116753 q = 1) : d196536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d196536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46585 q ha hb
    | true =>
      simp only [d21998, d196536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21999 q = 1) (hb : d116753 q = 1) : d196537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d196537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d196537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22000 q = 1) (hb : d116753 q = 1) : d196538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d196538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22000, d196538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22001 q = 1) (hb : d116753 q = 1) : d196539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d196539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d196539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22002 q = 1) (hb : d116753 q = 1) : d196540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d196540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d196540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22004 q = 1) (hb : d116753 q = 1) : d196542 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d196542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46588 q ha hb
    | true =>
      simp only [d22004, d196542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22005 q = 1) (hb : d116753 q = 1) : d196543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d196543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d196543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22006 q = 1) (hb : d116753 q = 1) : d196544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d196544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22006, d196544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22007 q = 1) (hb : d116753 q = 1) : d196545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d196545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d196545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22008 q = 1) (hb : d116753 q = 1) : d196546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d196546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d196546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22009 q = 1) (hb : d116753 q = 1) : d196547 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22009, d196547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22009, d196547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46595 (p : Pattern) (ha : d22018 p = 1) (hb : d116753 p = 1) : d196556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22004 q = 1) (hb : d116753 q = 1) : d196542 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d196542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46588 q ha hb
    | true =>
      simp only [d22004, d196542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22005 q = 1) (hb : d116753 q = 1) : d196543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d196543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d196543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22006 q = 1) (hb : d116753 q = 1) : d196544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d196544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22006, d196544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22007 q = 1) (hb : d116753 q = 1) : d196545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d196545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d196545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22008 q = 1) (hb : d116753 q = 1) : d196546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d196546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d196546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22018 q = 1) (hb : d116753 q = 1) : d196556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22018, d196556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22018, d196556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46596 (p : Pattern) (ha : d22069 p = 1) (hb : d116752 p = 1) : d196568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22068 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22058 q = 1) (hb : d116750 q = 1) : d22058 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22069 q = 1) (hb : d116752 q = 1) : d196568 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22069, d116752, d196568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22069, d116752, d196568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46597 (p : Pattern) (ha : d22097 p = 1) (hb : d116752 p = 1) : d196577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22096 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15023 q = 1) (hb : d116750 q = 1) : d15023 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22097 q = 1) (hb : d116752 q = 1) : d196577 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22097, d116752, d196577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22097, d116752, d196577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46598 (p : Pattern) (ha : d22103 p = 1) (hb : d116753 p = 1) : d196591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22098 q = 1) (hb : d116752 q = 1) : d196578 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d196578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
    | true =>
      simp only [d22098, d196578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46597 q ha hb
  have h2 (q : Pattern) (ha : d22099 q = 1) (hb : d116752 q = 1) : d196579 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d196579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d196579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22100 q = 1) (hb : d116752 q = 1) : d196580 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d196580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d196580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22101 q = 1) (hb : d116753 q = 1) : d196581 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d116753, d196581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22101, d116753, d196581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22102 q = 1) (hb : d116753 q = 1) : d196590 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22102, d196590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22102, d196590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22103 q = 1) (hb : d116753 q = 1) : d196591 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22103, d196591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22103, d196591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46599 (p : Pattern) (ha : d22197 p = 1) (hb : d116753 p = 1) : d196622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22104 q = 1) (hb : d116753 q = 1) : d196592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d196592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46598 q ha hb
    | true =>
      simp only [d22104, d196592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22105 q = 1) (hb : d116753 q = 1) : d196593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d196593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d196593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22194 q = 1) (hb : d116753 q = 1) : d196619 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22194, d196619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22194, d196619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22195 q = 1) (hb : d116753 q = 1) : d196620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22195, d196620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22195, d196620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22196 q = 1) (hb : d116753 q = 1) : d196621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22196, d196621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22196, d196621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22197 q = 1) (hb : d116753 q = 1) : d196622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22197, d196622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22197, d196622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46600 (p : Pattern) (ha : d22203 p = 1) (hb : d116753 p = 1) : d196628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22198 q = 1) (hb : d116753 q = 1) : d196623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22198, d196623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46599 q ha hb
    | true =>
      simp only [d22198, d196623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22199 q = 1) (hb : d116753 q = 1) : d196624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22199, d196624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22199, d196624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22200 q = 1) (hb : d116753 q = 1) : d196625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22200, d196625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22200, d196625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22201 q = 1) (hb : d116753 q = 1) : d196626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22201, d196626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22201, d196626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22202 q = 1) (hb : d116753 q = 1) : d196627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22202, d196627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22202, d196627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22203 q = 1) (hb : d116753 q = 1) : d196628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22203, d196628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22203, d196628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46601 (p : Pattern) (ha : d21818 p = 1) (hb : d116753 p = 1) : d196465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46582 q ha hb
    | true =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d116753 q = 1) : d196438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d116753 q = 1) : d196464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d196464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d196464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21818 q = 1) (hb : d116753 q = 1) : d196465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21818, d196465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21818, d196465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46602 (p : Pattern) (ha : d21820 p = 1) (hb : d116753 p = 1) : d196467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d116753 q = 1) : d196441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d116753 q = 1) : d196442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d116753 q = 1) : d196466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d196466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d196466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21820 q = 1) (hb : d116753 q = 1) : d196467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21820, d196467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21820, d196467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46603 (p : Pattern) (ha : d21827 p = 1) (hb : d116753 p = 1) : d196474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46582 q ha hb
    | true =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d116753 q = 1) : d196472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d196472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d196472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d116753 q = 1) : d196473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d196473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d196473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21827 q = 1) (hb : d116753 q = 1) : d196474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21827, d196474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21827, d196474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46604 (p : Pattern) (ha : d21830 p = 1) (hb : d116753 p = 1) : d196477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d116753 q = 1) : d196441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d116753 q = 1) : d196475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d196475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d196475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d116753 q = 1) : d196476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d196476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d196476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21830 q = 1) (hb : d116753 q = 1) : d196477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21830, d196477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21830, d196477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46605 (p : Pattern) (ha : d21846 p = 1) (hb : d116752 p = 1) : d196481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21839 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21845 q = 1) (hb : d116750 q = 1) : d21845 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21846 q = 1) (hb : d116752 q = 1) : d196481 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21846, d116752, d196481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21846, d116752, d196481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46606 (p : Pattern) (ha : d21862 p = 1) (hb : d116753 p = 1) : d196487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21847 q = 1) (hb : d116752 q = 1) : d196482 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21847, d196482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46605 q ha hb
    | true =>
      simp only [d21847, d196482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46579 q ha hb
  have h2 (q : Pattern) (ha : d21848 q = 1) (hb : d116752 q = 1) : d196483 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21848, d196483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21848, d196483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21849 q = 1) (hb : d116752 q = 1) : d196484 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21849, d196484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21849, d196484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21859 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21860 q = 1) (hb : d116753 q = 1) : d196485 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21860, d116753, d196485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21860, d116753, d196485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21762 q = 1) (hb : d116752 q = 1) : d196420 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46579 q ha hb
    | true =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
  have h7 (q : Pattern) (ha : d21763 q = 1) (hb : d116752 q = 1) : d196421 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21764 q = 1) (hb : d116752 q = 1) : d196422 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21775 q = 1) (hb : d116753 q = 1) : d196423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21861 q = 1) (hb : d116753 q = 1) : d196486 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21861, d196486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21861, d196486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21862 q = 1) (hb : d116753 q = 1) : d196487 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21862, d196487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21862, d196487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46607 (p : Pattern) (ha : d21873 p = 1) (hb : d116753 p = 1) : d196493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d116753 q = 1) : d196488 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46606 q ha hb
    | true =>
      simp only [d21863, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d116753 q = 1) : d196489 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46591 q ha hb
    | true =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d116753 q = 1) : d196490 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d196490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d196490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d116753 q = 1) : d196491 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d196491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d196491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d116753 q = 1) : d196492 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d196492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d196492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21873 q = 1) (hb : d116753 q = 1) : d196493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21873, d196493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21873, d196493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46608 (p : Pattern) (ha : d21948 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21948 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21948, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21948, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46609 (p : Pattern) (ha : d21954 p = 1) (hb : d116753 p = 1) : d196501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d116752 q = 1) : d196420 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46579 q ha hb
    | true =>
      simp only [d21762, d196420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d116752 q = 1) : d196421 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d196421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d116752 q = 1) : d196422 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d196422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21775 q = 1) (hb : d116753 q = 1) : d196423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d116753, d196423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21949 q = 1) (hb : d116752 q = 1) : d196496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21949, d196496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46580 q ha hb
    | true =>
      simp only [d21949, d196496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46608 q ha hb
  have h7 (q : Pattern) (ha : d21950 q = 1) (hb : d116752 q = 1) : d196497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21950, d196497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21950, d196497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21951 q = 1) (hb : d116752 q = 1) : d196498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21951, d196498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21951, d196498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21952 q = 1) (hb : d116753 q = 1) : d196499 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21952, d116753, d196499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21952, d116753, d196499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21953 q = 1) (hb : d116753 q = 1) : d196500 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21953, d196500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21953, d196500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21954 q = 1) (hb : d116753 q = 1) : d196501 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21954, d196501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21954, d196501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46610 (p : Pattern) (ha : d21960 p = 1) (hb : d116753 p = 1) : d196507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d116753 q = 1) : d196502 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d196502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46609 q ha hb
    | true =>
      simp only [d21955, d196502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d116753 q = 1) : d196503 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d196503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d196503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d116753 q = 1) : d196504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d196504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d196504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d116753 q = 1) : d196505 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d196505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d196505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d116753 q = 1) : d196506 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d196506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d196506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21960 q = 1) (hb : d116753 q = 1) : d196507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21960, d196507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21960, d196507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46611 (p : Pattern) (ha : d116753 p = 1) (hb : d150159 p = 1) : d196513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d116753 q = 1) : d196468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d196468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46601 q ha hb
    | true =>
      simp only [d21821, d196468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46602 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d116753 q = 1) : d196469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d196469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d196469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d116753 q = 1) : d196470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d196470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d196470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d116753 q = 1) : d196471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d196471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d196471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d116753 q = 1) : d196478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d196478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46603 q ha hb
    | true =>
      simp only [d21831, d196478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46604 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d116753 q = 1) : d196479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d196479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d196479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d116753 q = 1) : d196480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d196480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d196480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d116753 q = 1) : d196494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d196494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46607 q ha hb
    | true =>
      simp only [d21878, d196494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46592 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150155 q = 1) : d196495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d196495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150155, d196495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d116753 q = 1) : d196508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d196508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46610 q ha hb
    | true =>
      simp only [d21961, d196508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d116753 q = 1) : d196509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d196509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d196509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150156 q = 1) : d196510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d196510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d196510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150157 q = 1) : d196511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d196511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150157, d196511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150158 q = 1) : d196512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d196512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150158, d196512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150159 q = 1) : d196513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d196513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150159, d196513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46612 (p : Pattern) (ha : d21967 p = 1) (hb : d116753 p = 1) : d196514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46582 q ha hb
    | true =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d116753 q = 1) : d196438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d116753 q = 1) : d196464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d196464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d196464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21967 q = 1) (hb : d116753 q = 1) : d196514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21967, d196514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21967, d196514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46613 (p : Pattern) (ha : d21968 p = 1) (hb : d116753 p = 1) : d196515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d116753 q = 1) : d196441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d116753 q = 1) : d196442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d196442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d116753 q = 1) : d196466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d196466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d196466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21968 q = 1) (hb : d116753 q = 1) : d196515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21968, d196515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21968, d196515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46614 (p : Pattern) (ha : d21973 p = 1) (hb : d116753 p = 1) : d196520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46582 q ha hb
    | true =>
      simp only [d21784, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d116753 q = 1) : d196472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d196472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d196472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d116753 q = 1) : d196473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d196473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d196473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21973 q = 1) (hb : d116753 q = 1) : d196520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21973, d196520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21973, d196520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46615 (p : Pattern) (ha : d21974 p = 1) (hb : d116753 p = 1) : d196521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d116753 q = 1) : d196441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d196441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d116753 q = 1) : d196475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d196475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d196475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d116753 q = 1) : d196476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d196476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d196476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21974 q = 1) (hb : d116753 q = 1) : d196521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21974, d196521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21974, d196521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46616 (p : Pattern) (ha : d21978 p = 1) (hb : d116753 p = 1) : d196525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d116753 q = 1) : d196488 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46606 q ha hb
    | true =>
      simp only [d21863, d196488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d116753 q = 1) : d196489 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d196489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46591 q ha hb
    | true =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d116753 q = 1) : d196490 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d196490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d196490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d116753 q = 1) : d196491 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d196491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d196491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d116753 q = 1) : d196492 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d196492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d196492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21978 q = 1) (hb : d116753 q = 1) : d196525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21978, d196525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21978, d196525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46617 (p : Pattern) (ha : d21979 p = 1) (hb : d116753 p = 1) : d196453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d116753 q = 1) : d196431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46591 q ha hb
    | true =>
      simp only [d21868, d196431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d116753 q = 1) : d196432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d196432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d116753 q = 1) : d196435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46583 q ha hb
    | true =>
      simp only [d21788, d196435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d116753 q = 1) : d196436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d196436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d116753 q = 1) : d196437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d196437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d116753 q = 1) : d196438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d196438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d116753 q = 1) : d196439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d196439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21979 q = 1) (hb : d116753 q = 1) : d196453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21979, d196453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21979, d196453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46618 (p : Pattern) (ha : d21985 p = 1) (hb : d116753 p = 1) : d196528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d116753 q = 1) : d196502 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d196502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46609 q ha hb
    | true =>
      simp only [d21955, d196502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d116753 q = 1) : d196503 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d196503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d196503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d116753 q = 1) : d196504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d196504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d196504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d116753 q = 1) : d196505 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d196505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d196505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d116753 q = 1) : d196506 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d196506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d196506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21985 q = 1) (hb : d116753 q = 1) : d196528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21985, d196528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21985, d196528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46619 (p : Pattern) (ha : d116753 p = 1) (hb : d150164 p = 1) : d196534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d116753 q = 1) : d196468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d196468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46601 q ha hb
    | true =>
      simp only [d21821, d196468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46602 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d116753 q = 1) : d196469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d196469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d196469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d116753 q = 1) : d196470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d196470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d196470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d116753 q = 1) : d196471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d196471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d196471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d116753 q = 1) : d196478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d196478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46603 q ha hb
    | true =>
      simp only [d21831, d196478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46604 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d116753 q = 1) : d196479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d196479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d196479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d116753 q = 1) : d196480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d196480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d196480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d116753 q = 1) : d196494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d196494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46607 q ha hb
    | true =>
      simp only [d21878, d196494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46592 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150155 q = 1) : d196495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d196495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150155, d196495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d116753 q = 1) : d196508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d196508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46610 q ha hb
    | true =>
      simp only [d21961, d196508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d116753 q = 1) : d196509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d196509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d196509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150156 q = 1) : d196510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d196510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d196510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150157 q = 1) : d196511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d196511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150157, d196511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150158 q = 1) : d196512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d196512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150158, d196512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21969 q = 1) (hb : d116753 q = 1) : d196516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21969, d196516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46612 q ha hb
    | true =>
      simp only [d21969, d196516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46613 q ha hb
  have h16 (q : Pattern) (ha : d21970 q = 1) (hb : d116753 q = 1) : d196517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21970, d196517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21970, d196517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21971 q = 1) (hb : d116753 q = 1) : d196518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21971, d196518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21971, d196518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21972 q = 1) (hb : d116753 q = 1) : d196519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21972, d196519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21972, d196519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21975 q = 1) (hb : d116753 q = 1) : d196522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21975, d196522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46614 q ha hb
    | true =>
      simp only [d21975, d196522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46615 q ha hb
  have h20 (q : Pattern) (ha : d21976 q = 1) (hb : d116753 q = 1) : d196523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21976, d196523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21976, d196523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21977 q = 1) (hb : d116753 q = 1) : d196524 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21977, d196524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21977, d196524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21980 q = 1) (hb : d116753 q = 1) : d196526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d196526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46616 q ha hb
    | true =>
      simp only [d21980, d196526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46617 q ha hb
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150160 q = 1) : d196527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d196527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150160, d196527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21986 q = 1) (hb : d116753 q = 1) : d196529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d196529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46618 q ha hb
    | true =>
      simp only [d21986, d196529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21987 q = 1) (hb : d116753 q = 1) : d196530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d196530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21987, d196530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116753 q = 1) (hb : d150161 q = 1) : d196531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d196531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150161, d196531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116753 q = 1) (hb : d150162 q = 1) : d196532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d196532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150162, d196532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116753 q = 1) (hb : d150163 q = 1) : d196533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d196533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150163, d196533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116753 q = 1) (hb : d150164 q = 1) : d196534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d196534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150164, d196534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro46620 (p : Pattern) (ha : d116753 p = 1) (hb : d150171 p = 1) : d196554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21980 q = 1) (hb : d116753 q = 1) : d196526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d196526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46616 q ha hb
    | true =>
      simp only [d21980, d196526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46617 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150160 q = 1) : d196527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d196527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150160, d196527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21986 q = 1) (hb : d116753 q = 1) : d196529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d196529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46618 q ha hb
    | true =>
      simp only [d21986, d196529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21987 q = 1) (hb : d116753 q = 1) : d196530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d196530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21987, d196530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150161 q = 1) : d196531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d196531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150161, d196531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150169 q = 1) : d196552 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d196552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150169, d196552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150170 q = 1) : d196553 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d196553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150170, d196553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150171 q = 1) : d196554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d196554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150171, d196554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46621 (p : Pattern) (ha : d22042 p = 1) (hb : d116752 p = 1) : d196562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22032 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22041 q = 1) (hb : d116750 q = 1) : d22041 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22042 q = 1) (hb : d116752 q = 1) : d196562 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22042, d116752, d196562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22042, d116752, d196562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46622 (p : Pattern) (ha : d22049 p = 1) (hb : d116752 p = 1) : d196563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22047 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22048 q = 1) (hb : d116750 q = 1) : d22048 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22049 q = 1) (hb : d116752 q = 1) : d196563 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22049, d116752, d196563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22049, d116752, d196563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46623 (p : Pattern) (ha : d22084 p = 1) (hb : d116753 p = 1) : d196574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22050 q = 1) (hb : d116752 q = 1) : d196564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22050, d196564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46621 q ha hb
    | true =>
      simp only [d22050, d196564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46622 q ha hb
  have h2 (q : Pattern) (ha : d22051 q = 1) (hb : d116752 q = 1) : d196565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22051, d196565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22051, d196565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22052 q = 1) (hb : d116752 q = 1) : d196566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22052, d196566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22052, d196566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22062 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22063 q = 1) (hb : d116753 q = 1) : d196567 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22063, d116753, d196567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22063, d116753, d196567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22070 q = 1) (hb : d116752 q = 1) : d196569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46622 q ha hb
    | true =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
  have h7 (q : Pattern) (ha : d22071 q = 1) (hb : d116752 q = 1) : d196570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22072 q = 1) (hb : d116752 q = 1) : d196571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22081 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22082 q = 1) (hb : d116753 q = 1) : d196572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d22083 q = 1) (hb : d116753 q = 1) : d196573 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22083, d196573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22083, d196573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22084 q = 1) (hb : d116753 q = 1) : d196574 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22084, d196574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22084, d196574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46624 (p : Pattern) (ha : d22078 p = 1) (hb : d116752 p = 1) : d196577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22077 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15023 q = 1) (hb : d116750 q = 1) : d15023 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22078 q = 1) (hb : d116752 q = 1) : d196577 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22078, d116752, d196577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22078, d116752, d196577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46625 (p : Pattern) (ha : d22089 p = 1) (hb : d116753 p = 1) : d196583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d116752 q = 1) : d196569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46622 q ha hb
    | true =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d116752 q = 1) : d196570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d116752 q = 1) : d196571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22081 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22082 q = 1) (hb : d116753 q = 1) : d196572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22079 q = 1) (hb : d116752 q = 1) : d196578 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d196578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
    | true =>
      simp only [d22079, d196578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46624 q ha hb
  have h7 (q : Pattern) (ha : d22080 q = 1) (hb : d116752 q = 1) : d196579 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d196579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d196579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22081 q = 1) (hb : d116752 q = 1) : d196580 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d196580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d196580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22087 q = 1) (hb : d116753 q = 1) : d196581 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22087, d116753, d196581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22087, d116753, d196581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22088 q = 1) (hb : d116753 q = 1) : d196582 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22088, d196582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22088, d196582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22089 q = 1) (hb : d116753 q = 1) : d196583 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22089, d196583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22089, d196583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46626 (p : Pattern) (ha : d22095 p = 1) (hb : d116753 p = 1) : d196589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22085 q = 1) (hb : d116753 q = 1) : d196575 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22085, d196575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46623 q ha hb
    | true =>
      simp only [d22085, d196575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22086 q = 1) (hb : d116753 q = 1) : d196576 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22086, d196576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22086, d196576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22090 q = 1) (hb : d116753 q = 1) : d196584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d196584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46625 q ha hb
    | true =>
      simp only [d22090, d196584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22091 q = 1) (hb : d116753 q = 1) : d196585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d196585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d196585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22092 q = 1) (hb : d116753 q = 1) : d196586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22092, d196586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22092, d196586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22093 q = 1) (hb : d116753 q = 1) : d196587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22093, d196587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22093, d196587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22094 q = 1) (hb : d116753 q = 1) : d196588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22094, d196588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22094, d196588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22095 q = 1) (hb : d116753 q = 1) : d196589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22095, d196589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22095, d196589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46627 (p : Pattern) (ha : d22109 p = 1) (hb : d116753 p = 1) : d196597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22090 q = 1) (hb : d116753 q = 1) : d196584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d196584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46625 q ha hb
    | true =>
      simp only [d22090, d196584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22091 q = 1) (hb : d116753 q = 1) : d196585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d196585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d196585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d116753 q = 1) : d196592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d196592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46598 q ha hb
    | true =>
      simp only [d22104, d196592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d116753 q = 1) : d196593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d196593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d196593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22106 q = 1) (hb : d116753 q = 1) : d196594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22106, d196594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22106, d196594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22107 q = 1) (hb : d116753 q = 1) : d196595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22107, d196595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22107, d196595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22108 q = 1) (hb : d116753 q = 1) : d196596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22108, d196596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22108, d196596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22109 q = 1) (hb : d116753 q = 1) : d196597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22109, d196597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22109, d196597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46628 (p : Pattern) (ha : d22174 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22096 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22174 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22174, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22174, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46629 (p : Pattern) (ha : d22180 p = 1) (hb : d116753 p = 1) : d196605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d116752 q = 1) : d196569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46622 q ha hb
    | true =>
      simp only [d22070, d196569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d116752 q = 1) : d196570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d196570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d116752 q = 1) : d196571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d196571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22081 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22082 q = 1) (hb : d116753 q = 1) : d196572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d116753, d196572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22175 q = 1) (hb : d116752 q = 1) : d196600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22175, d196600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46596 q ha hb
    | true =>
      simp only [d22175, d196600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46628 q ha hb
  have h7 (q : Pattern) (ha : d22176 q = 1) (hb : d116752 q = 1) : d196601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22176, d196601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22176, d196601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22177 q = 1) (hb : d116752 q = 1) : d196602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22177, d196602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22177, d196602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22178 q = 1) (hb : d116753 q = 1) : d196603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22178, d116753, d196603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22178, d116753, d196603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22179 q = 1) (hb : d116753 q = 1) : d196604 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22179, d196604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22179, d196604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22180 q = 1) (hb : d116753 q = 1) : d196605 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22180, d196605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22180, d196605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46630 (p : Pattern) (ha : d22186 p = 1) (hb : d116753 p = 1) : d196611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22181 q = 1) (hb : d116753 q = 1) : d196606 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22181, d196606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46629 q ha hb
    | true =>
      simp only [d22181, d196606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22182 q = 1) (hb : d116753 q = 1) : d196607 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22182, d196607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22182, d196607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22183 q = 1) (hb : d116753 q = 1) : d196608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22183, d196608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22183, d196608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22184 q = 1) (hb : d116753 q = 1) : d196609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22184, d196609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22184, d196609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22185 q = 1) (hb : d116753 q = 1) : d196610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22185, d196610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22185, d196610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22186 q = 1) (hb : d116753 q = 1) : d196611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22186, d196611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22186, d196611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46631 (p : Pattern) (ha : d116753 p = 1) (hb : d150181 p = 1) : d196617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22110 q = 1) (hb : d116753 q = 1) : d196598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22110, d196598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46626 q ha hb
    | true =>
      simp only [d22110, d196598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46627 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150177 q = 1) : d196599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d196599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150177, d196599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22187 q = 1) (hb : d116753 q = 1) : d196612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22187, d196612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46630 q ha hb
    | true =>
      simp only [d22187, d196612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22188 q = 1) (hb : d116753 q = 1) : d196613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22188, d196613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22188, d196613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150178 q = 1) : d196614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d196614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150178, d196614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150179 q = 1) : d196615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d196615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150179, d196615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150180 q = 1) : d196616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d196616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150180, d196616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150181 q = 1) : d196617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d196617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150181, d196617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46632 (p : Pattern) (ha : d116753 p = 1) (hb : d150187 p = 1) : d196634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21804 q = 1) (hb : d116753 q = 1) : d196451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21804, d196451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21804, d196451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46586 q ha hb
  have h2 (q : Pattern) (ha : d21805 q = 1) (hb : d116753 q = 1) : d196452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21805, d196452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21805, d196452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21814 q = 1) (hb : d116753 q = 1) : d196461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d196461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46586 q ha hb
    | true =>
      simp only [d21814, d196461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46589 q ha hb
  have h4 (q : Pattern) (ha : d21815 q = 1) (hb : d116753 q = 1) : d196462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d196462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21815, d196462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21816 q = 1) (hb : d116753 q = 1) : d196463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21816, d196463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21816, d196463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150165 q = 1) : d196535 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d196535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46611 q ha hb
    | true =>
      simp only [d150165, d196535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46619 q ha hb
  have h7 (q : Pattern) (ha : d22010 q = 1) (hb : d116753 q = 1) : d196548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22010, d196548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46593 q ha hb
    | true =>
      simp only [d22010, d196548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46594 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150166 q = 1) : d196549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d196549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150166, d196549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150167 q = 1) : d196550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d196550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150167, d196550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150168 q = 1) : d196551 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d196551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150168, d196551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150172 q = 1) : d196555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d196555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150172, d196555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46620 q ha hb
  have h12 (q : Pattern) (ha : d22019 q = 1) (hb : d116753 q = 1) : d196557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22019, d196557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22019, d196557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46595 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150173 q = 1) : d196558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d196558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150173, d196558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150174 q = 1) : d196559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d196559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150174, d196559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150175 q = 1) : d196560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d196560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150175, d196560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150176 q = 1) : d196561 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d196561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150176, d196561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116753 q = 1) (hb : d150182 q = 1) : d196618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d196618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150182, d196618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46631 q ha hb
  have h18 (q : Pattern) (ha : d22204 q = 1) (hb : d116753 q = 1) : d196629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22204, d196629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22204, d196629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46600 q ha hb
  have h19 (q : Pattern) (ha : d116753 q = 1) (hb : d150183 q = 1) : d196630 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d196630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150183, d196630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116753 q = 1) (hb : d150184 q = 1) : d196631 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d196631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150184, d196631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116753 q = 1) (hb : d150185 q = 1) : d196632 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d196632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150185, d196632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116753 q = 1) (hb : d150186 q = 1) : d196633 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d196633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150186, d196633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150187 q = 1) : d196634 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d196634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150187, d196634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46633 (p : Pattern) (ha : d116753 p = 1) (hb : d150193 p = 1) : d196640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150188 q = 1) : d196635 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d196635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150188, d196635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46632 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150189 q = 1) : d196636 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d196636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150189, d196636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150190 q = 1) : d196637 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d196637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150190, d196637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150191 q = 1) : d196638 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d196638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150191, d196638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150192 q = 1) : d196639 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d196639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150192, d196639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150193 q = 1) : d196640 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d196640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150193, d196640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46634 (p : Pattern) (ha : d22231 p = 1) (hb : d116752 p = 1) : d196644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22224 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22230 q = 1) (hb : d116750 q = 1) : d22230 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22231 q = 1) (hb : d116752 q = 1) : d196644 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22231, d116752, d196644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22231, d116752, d196644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46635 (p : Pattern) (ha : d22239 p = 1) (hb : d116752 p = 1) : d196645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22237 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22238 q = 1) (hb : d116750 q = 1) : d22238 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22239 q = 1) (hb : d116752 q = 1) : d196645 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22239, d116752, d196645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22239, d116752, d196645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46636 (p : Pattern) (ha : d22255 p = 1) (hb : d116752 p = 1) : d196650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22254 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15165 q = 1) (hb : d116750 q = 1) : d15165 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22255 q = 1) (hb : d116752 q = 1) : d196650 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22255, d116752, d196650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22255, d116752, d196650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46637 (p : Pattern) (ha : d22261 p = 1) (hb : d116753 p = 1) : d196656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d116752 q = 1) : d196646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46634 q ha hb
    | true =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d116752 q = 1) : d196647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d116752 q = 1) : d196648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22252 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22253 q = 1) (hb : d116753 q = 1) : d196649 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22256 q = 1) (hb : d116752 q = 1) : d196651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d196651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
    | true =>
      simp only [d22256, d196651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46636 q ha hb
  have h7 (q : Pattern) (ha : d22257 q = 1) (hb : d116752 q = 1) : d196652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d196652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d196652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22258 q = 1) (hb : d116752 q = 1) : d196653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d196653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d196653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22259 q = 1) (hb : d116753 q = 1) : d196654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d116753, d196654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22259, d116753, d196654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22260 q = 1) (hb : d116753 q = 1) : d196655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22260, d196655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22260, d196655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22261 q = 1) (hb : d116753 q = 1) : d196656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22261, d196656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22261, d196656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46638 (p : Pattern) (ha : d22265 p = 1) (hb : d116753 p = 1) : d196660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22256 q = 1) (hb : d116752 q = 1) : d196651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d196651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
    | true =>
      simp only [d22256, d196651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46636 q ha hb
  have h2 (q : Pattern) (ha : d22257 q = 1) (hb : d116752 q = 1) : d196652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d196652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d196652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22258 q = 1) (hb : d116752 q = 1) : d196653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d196653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d196653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22259 q = 1) (hb : d116753 q = 1) : d196654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d116753, d196654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22259, d116753, d196654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22264 q = 1) (hb : d116753 q = 1) : d196659 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22264, d196659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22264, d196659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22265 q = 1) (hb : d116753 q = 1) : d196660 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22265, d196660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22265, d196660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46639 (p : Pattern) (ha : d22271 p = 1) (hb : d116753 p = 1) : d196666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46637 q ha hb
    | true =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d116753 q = 1) : d196664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d116753 q = 1) : d196665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22271 q = 1) (hb : d116753 q = 1) : d196666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22271, d196666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22271, d196666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46640 (p : Pattern) (ha : d22275 p = 1) (hb : d116753 p = 1) : d196670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d116753 q = 1) : d196667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d116753 q = 1) : d196668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d116753 q = 1) : d196669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d196669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d196669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22275 q = 1) (hb : d116753 q = 1) : d196670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22275, d196670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22275, d196670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46641 (p : Pattern) (ha : d22281 p = 1) (hb : d116753 p = 1) : d196676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d116753 q = 1) : d196671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d196671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46639 q ha hb
    | true =>
      simp only [d22276, d196671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46640 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d116753 q = 1) : d196672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d196672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d196672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d116753 q = 1) : d196673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d196673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d196673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d116753 q = 1) : d196674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d196674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d196674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d116753 q = 1) : d196675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d196675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d196675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22281 q = 1) (hb : d116753 q = 1) : d196676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d196676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d196676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46642 (p : Pattern) (ha : d22284 p = 1) (hb : d116753 p = 1) : d196679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46637 q ha hb
    | true =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d116753 q = 1) : d196664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d116753 q = 1) : d196665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22284 q = 1) (hb : d116753 q = 1) : d196679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22284, d196679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22284, d196679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46643 (p : Pattern) (ha : d22285 p = 1) (hb : d116753 p = 1) : d196680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d116753 q = 1) : d196667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d116753 q = 1) : d196668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d116753 q = 1) : d196669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d196669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d196669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22285 q = 1) (hb : d116753 q = 1) : d196680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22285, d196680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22285, d196680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46644 (p : Pattern) (ha : d22291 p = 1) (hb : d116753 p = 1) : d196686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d116753 q = 1) : d196671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d196671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46639 q ha hb
    | true =>
      simp only [d22276, d196671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46640 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d116753 q = 1) : d196672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d196672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d196672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d116753 q = 1) : d196673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d196673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d196673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d116753 q = 1) : d196674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d196674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d196674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d116753 q = 1) : d196675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d196675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d196675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22286 q = 1) (hb : d116753 q = 1) : d196681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d196681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46642 q ha hb
    | true =>
      simp only [d22286, d196681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46643 q ha hb
  have h7 (q : Pattern) (ha : d22287 q = 1) (hb : d116753 q = 1) : d196682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d196682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d196682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22288 q = 1) (hb : d116753 q = 1) : d196683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d196683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22288, d196683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22289 q = 1) (hb : d116753 q = 1) : d196684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d196684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d196684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22290 q = 1) (hb : d116753 q = 1) : d196685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d196685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d196685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22291 q = 1) (hb : d116753 q = 1) : d196686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d196686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22291, d196686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46645 (p : Pattern) (ha : d22249 p = 1) (hb : d116752 p = 1) : d196650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22248 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15165 q = 1) (hb : d116750 q = 1) : d15165 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22249 q = 1) (hb : d116752 q = 1) : d196650 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22249, d116752, d196650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22249, d116752, d196650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46646 (p : Pattern) (ha : d22340 p = 1) (hb : d116753 p = 1) : d196656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d116752 q = 1) : d196646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46634 q ha hb
    | true =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d116752 q = 1) : d196647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d116752 q = 1) : d196648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22252 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22253 q = 1) (hb : d116753 q = 1) : d196649 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22250 q = 1) (hb : d116752 q = 1) : d196651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d196651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
    | true =>
      simp only [d22250, d196651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46645 q ha hb
  have h7 (q : Pattern) (ha : d22251 q = 1) (hb : d116752 q = 1) : d196652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d196652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d196652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22252 q = 1) (hb : d116752 q = 1) : d196653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d196653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d196653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22338 q = 1) (hb : d116753 q = 1) : d196654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22338, d116753, d196654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22338, d116753, d196654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22339 q = 1) (hb : d116753 q = 1) : d196655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22339, d196655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22339, d196655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22340 q = 1) (hb : d116753 q = 1) : d196656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22340, d196656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22340, d196656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46647 (p : Pattern) (ha : d22350 p = 1) (hb : d116753 p = 1) : d196666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46646 q ha hb
    | true =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d116753 q = 1) : d196664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d116753 q = 1) : d196665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22350 q = 1) (hb : d116753 q = 1) : d196666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22350, d196666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22350, d196666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46648 (p : Pattern) (ha : d22476 p = 1) (hb : d116753 p = 1) : d196767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22466 q = 1) (hb : d116753 q = 1) : d196671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22466, d196671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46647 q ha hb
    | true =>
      simp only [d22466, d196671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46640 q ha hb
  have h2 (q : Pattern) (ha : d22467 q = 1) (hb : d116753 q = 1) : d196672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22467, d196672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22467, d196672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22468 q = 1) (hb : d116753 q = 1) : d196673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22468, d196673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22468, d196673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22469 q = 1) (hb : d116753 q = 1) : d196674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22469, d196674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22469, d196674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22470 q = 1) (hb : d116753 q = 1) : d196675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22470, d196675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22470, d196675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22471 q = 1) (hb : d116753 q = 1) : d196762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d196762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46640 q ha hb
    | true =>
      simp only [d22471, d196762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22472 q = 1) (hb : d116753 q = 1) : d196763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d196763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d196763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22473 q = 1) (hb : d116753 q = 1) : d196764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d196764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22473, d196764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22474 q = 1) (hb : d116753 q = 1) : d196765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d196765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d196765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22475 q = 1) (hb : d116753 q = 1) : d196766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d196766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d196766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22476 q = 1) (hb : d116753 q = 1) : d196767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22476, d196767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22476, d196767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46649 (p : Pattern) (ha : d22482 p = 1) (hb : d116753 p = 1) : d196773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22471 q = 1) (hb : d116753 q = 1) : d196762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d196762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46640 q ha hb
    | true =>
      simp only [d22471, d196762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22472 q = 1) (hb : d116753 q = 1) : d196763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d196763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d196763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22473 q = 1) (hb : d116753 q = 1) : d196764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d196764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22473, d196764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22474 q = 1) (hb : d116753 q = 1) : d196765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d196765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d196765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22475 q = 1) (hb : d116753 q = 1) : d196766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d196766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d196766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22477 q = 1) (hb : d116753 q = 1) : d196768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d196768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46643 q ha hb
    | true =>
      simp only [d22477, d196768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22478 q = 1) (hb : d116753 q = 1) : d196769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d196769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d196769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22479 q = 1) (hb : d116753 q = 1) : d196770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d196770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22479, d196770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22480 q = 1) (hb : d116753 q = 1) : d196771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d196771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d196771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22481 q = 1) (hb : d116753 q = 1) : d196772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d196772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d196772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22482 q = 1) (hb : d116753 q = 1) : d196773 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22482, d196773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22482, d196773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46650 (p : Pattern) (ha : d22491 p = 1) (hb : d116753 p = 1) : d196782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22477 q = 1) (hb : d116753 q = 1) : d196768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d196768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46643 q ha hb
    | true =>
      simp only [d22477, d196768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22478 q = 1) (hb : d116753 q = 1) : d196769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d196769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d196769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22479 q = 1) (hb : d116753 q = 1) : d196770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d196770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22479, d196770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22480 q = 1) (hb : d116753 q = 1) : d196771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d196771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d196771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22481 q = 1) (hb : d116753 q = 1) : d196772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d196772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d196772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22491 q = 1) (hb : d116753 q = 1) : d196782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22491, d196782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22491, d196782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46651 (p : Pattern) (ha : d22534 p = 1) (hb : d116752 p = 1) : d196794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22533 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22523 q = 1) (hb : d116750 q = 1) : d22523 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22534 q = 1) (hb : d116752 q = 1) : d196794 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22534, d116752, d196794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22534, d116752, d196794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46652 (p : Pattern) (ha : d22562 p = 1) (hb : d116752 p = 1) : d196803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22561 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15416 q = 1) (hb : d116750 q = 1) : d15416 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22562 q = 1) (hb : d116752 q = 1) : d196803 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22562, d116752, d196803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22562, d116752, d196803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46653 (p : Pattern) (ha : d22568 p = 1) (hb : d116753 p = 1) : d196817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22563 q = 1) (hb : d116752 q = 1) : d196804 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d196804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
    | true =>
      simp only [d22563, d196804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46652 q ha hb
  have h2 (q : Pattern) (ha : d22564 q = 1) (hb : d116752 q = 1) : d196805 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d196805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d196805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22565 q = 1) (hb : d116752 q = 1) : d196806 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d196806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d196806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22566 q = 1) (hb : d116753 q = 1) : d196807 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d116753, d196807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22566, d116753, d196807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22567 q = 1) (hb : d116753 q = 1) : d196816 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22567, d196816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22567, d196816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22568 q = 1) (hb : d116753 q = 1) : d196817 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22568, d196817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22568, d196817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46654 (p : Pattern) (ha : d22662 p = 1) (hb : d116753 p = 1) : d196848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22569 q = 1) (hb : d116753 q = 1) : d196818 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d196818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46653 q ha hb
    | true =>
      simp only [d22569, d196818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22570 q = 1) (hb : d116753 q = 1) : d196819 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d196819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d196819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22659 q = 1) (hb : d116753 q = 1) : d196845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22659, d196845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22659, d196845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22660 q = 1) (hb : d116753 q = 1) : d196846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22660, d196846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22660, d196846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22661 q = 1) (hb : d116753 q = 1) : d196847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22661, d196847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22661, d196847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22662 q = 1) (hb : d116753 q = 1) : d196848 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22662, d196848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22662, d196848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46655 (p : Pattern) (ha : d22668 p = 1) (hb : d116753 p = 1) : d196854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22663 q = 1) (hb : d116753 q = 1) : d196849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22663, d196849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46654 q ha hb
    | true =>
      simp only [d22663, d196849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22664 q = 1) (hb : d116753 q = 1) : d196850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22664, d196850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22664, d196850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22665 q = 1) (hb : d116753 q = 1) : d196851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22665, d196851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22665, d196851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22666 q = 1) (hb : d116753 q = 1) : d196852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22666, d196852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22666, d196852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22667 q = 1) (hb : d116753 q = 1) : d196853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22667, d196853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22667, d196853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22668 q = 1) (hb : d116753 q = 1) : d196854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22668, d196854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22668, d196854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46656 (p : Pattern) (ha : d22296 p = 1) (hb : d116753 p = 1) : d196691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46637 q ha hb
    | true =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d116753 q = 1) : d196664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d116753 q = 1) : d196690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d196690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d196690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22296 q = 1) (hb : d116753 q = 1) : d196691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22296, d196691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22296, d196691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46657 (p : Pattern) (ha : d22298 p = 1) (hb : d116753 p = 1) : d196693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d116753 q = 1) : d196667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d116753 q = 1) : d196668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d116753 q = 1) : d196692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d196692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d196692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22298 q = 1) (hb : d116753 q = 1) : d196693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22298, d196693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22298, d196693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46658 (p : Pattern) (ha : d22305 p = 1) (hb : d116753 p = 1) : d196700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46637 q ha hb
    | true =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d116753 q = 1) : d196698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d196698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d196698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d116753 q = 1) : d196699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d196699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d196699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22305 q = 1) (hb : d116753 q = 1) : d196700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22305, d196700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22305, d196700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46659 (p : Pattern) (ha : d22308 p = 1) (hb : d116753 p = 1) : d196703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d116753 q = 1) : d196667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d116753 q = 1) : d196701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d196701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d196701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d116753 q = 1) : d196702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d196702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d196702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22308 q = 1) (hb : d116753 q = 1) : d196703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22308, d196703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22308, d196703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46660 (p : Pattern) (ha : d22319 p = 1) (hb : d116752 p = 1) : d196707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22317 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22318 q = 1) (hb : d116750 q = 1) : d22318 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22319 q = 1) (hb : d116752 q = 1) : d196707 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22319, d116752, d196707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22319, d116752, d196707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46661 (p : Pattern) (ha : d22335 p = 1) (hb : d116753 p = 1) : d196713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22320 q = 1) (hb : d116752 q = 1) : d196708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22320, d196708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46660 q ha hb
    | true =>
      simp only [d22320, d196708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46634 q ha hb
  have h2 (q : Pattern) (ha : d22321 q = 1) (hb : d116752 q = 1) : d196709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22321, d196709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22321, d196709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22322 q = 1) (hb : d116752 q = 1) : d196710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22322, d196710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22322, d196710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22333 q = 1) (hb : d116753 q = 1) : d196711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22333, d116753, d196711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22333, d116753, d196711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22240 q = 1) (hb : d116752 q = 1) : d196646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46634 q ha hb
    | true =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
  have h7 (q : Pattern) (ha : d22241 q = 1) (hb : d116752 q = 1) : d196647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22242 q = 1) (hb : d116752 q = 1) : d196648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22252 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22253 q = 1) (hb : d116753 q = 1) : d196649 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d22334 q = 1) (hb : d116753 q = 1) : d196712 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22334, d196712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22334, d196712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22335 q = 1) (hb : d116753 q = 1) : d196713 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22335, d196713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22335, d196713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46662 (p : Pattern) (ha : d22346 p = 1) (hb : d116753 p = 1) : d196719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d116753 q = 1) : d196714 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46661 q ha hb
    | true =>
      simp only [d22336, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d116753 q = 1) : d196715 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46646 q ha hb
    | true =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d116753 q = 1) : d196716 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d196716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d196716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d116753 q = 1) : d196717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d196717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d196717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d116753 q = 1) : d196718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d196718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d196718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22346 q = 1) (hb : d116753 q = 1) : d196719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22346, d196719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22346, d196719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46663 (p : Pattern) (ha : d22421 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22254 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22421 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22421, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22421, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46664 (p : Pattern) (ha : d22427 p = 1) (hb : d116753 p = 1) : d196727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22240 q = 1) (hb : d116752 q = 1) : d196646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46634 q ha hb
    | true =>
      simp only [d22240, d196646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
  have h2 (q : Pattern) (ha : d22241 q = 1) (hb : d116752 q = 1) : d196647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d196647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22242 q = 1) (hb : d116752 q = 1) : d196648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d196648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22252 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22253 q = 1) (hb : d116753 q = 1) : d196649 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22253, d116753, d196649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22422 q = 1) (hb : d116752 q = 1) : d196722 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22422, d196722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46635 q ha hb
    | true =>
      simp only [d22422, d196722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46663 q ha hb
  have h7 (q : Pattern) (ha : d22423 q = 1) (hb : d116752 q = 1) : d196723 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22423, d196723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22423, d196723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22424 q = 1) (hb : d116752 q = 1) : d196724 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22424, d196724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22424, d196724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22425 q = 1) (hb : d116753 q = 1) : d196725 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22425, d116753, d196725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22425, d116753, d196725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22426 q = 1) (hb : d116753 q = 1) : d196726 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22426, d196726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22426, d196726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22427 q = 1) (hb : d116753 q = 1) : d196727 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22427, d196727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22427, d196727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46665 (p : Pattern) (ha : d22433 p = 1) (hb : d116753 p = 1) : d196733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d116753 q = 1) : d196728 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d196728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46664 q ha hb
    | true =>
      simp only [d22428, d196728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d116753 q = 1) : d196729 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d196729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d196729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d116753 q = 1) : d196730 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d196730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d196730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d116753 q = 1) : d196731 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d196731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d196731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d116753 q = 1) : d196732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d196732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d196732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22433 q = 1) (hb : d116753 q = 1) : d196733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22433, d196733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22433, d196733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46666 (p : Pattern) (ha : d116753 p = 1) (hb : d150201 p = 1) : d196739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d116753 q = 1) : d196694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d196694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46656 q ha hb
    | true =>
      simp only [d22299, d196694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46657 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d116753 q = 1) : d196695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d196695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d196695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d116753 q = 1) : d196696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d196696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d196696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d116753 q = 1) : d196697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d196697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d196697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d116753 q = 1) : d196704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d196704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46658 q ha hb
    | true =>
      simp only [d22309, d196704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46659 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d116753 q = 1) : d196705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d196705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d196705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d116753 q = 1) : d196706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d196706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d196706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d116753 q = 1) : d196720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d196720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46662 q ha hb
    | true =>
      simp only [d22351, d196720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46647 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150197 q = 1) : d196721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d196721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150197, d196721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d116753 q = 1) : d196734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d196734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46665 q ha hb
    | true =>
      simp only [d22434, d196734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d116753 q = 1) : d196735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d196735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d196735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150198 q = 1) : d196736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d196736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d196736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150199 q = 1) : d196737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d196737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150199, d196737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150200 q = 1) : d196738 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d196738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150200, d196738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150201 q = 1) : d196739 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d196739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150201, d196739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46667 (p : Pattern) (ha : d22440 p = 1) (hb : d116753 p = 1) : d196740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46637 q ha hb
    | true =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d116753 q = 1) : d196664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d116753 q = 1) : d196690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d196690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d196690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22440 q = 1) (hb : d116753 q = 1) : d196740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22440, d196740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22440, d196740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46668 (p : Pattern) (ha : d22441 p = 1) (hb : d116753 p = 1) : d196741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d116753 q = 1) : d196667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d116753 q = 1) : d196668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d196668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d116753 q = 1) : d196692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d196692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d196692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22441 q = 1) (hb : d116753 q = 1) : d196741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22441, d196741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22441, d196741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46669 (p : Pattern) (ha : d22446 p = 1) (hb : d116753 p = 1) : d196746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46637 q ha hb
    | true =>
      simp only [d22262, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d116753 q = 1) : d196698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d196698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d196698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d116753 q = 1) : d196699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d196699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d196699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22446 q = 1) (hb : d116753 q = 1) : d196746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22446, d196746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22446, d196746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46670 (p : Pattern) (ha : d22447 p = 1) (hb : d116753 p = 1) : d196747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d116753 q = 1) : d196667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d196667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d116753 q = 1) : d196701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d196701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d196701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d116753 q = 1) : d196702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d196702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d196702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22447 q = 1) (hb : d116753 q = 1) : d196747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22447, d196747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22447, d196747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46671 (p : Pattern) (ha : d22451 p = 1) (hb : d116753 p = 1) : d196751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d116753 q = 1) : d196714 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46661 q ha hb
    | true =>
      simp only [d22336, d196714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d116753 q = 1) : d196715 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d196715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46646 q ha hb
    | true =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d116753 q = 1) : d196716 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d196716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d196716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d116753 q = 1) : d196717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d196717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d196717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d116753 q = 1) : d196718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d196718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d196718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22451 q = 1) (hb : d116753 q = 1) : d196751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22451, d196751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22451, d196751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46672 (p : Pattern) (ha : d22452 p = 1) (hb : d116753 p = 1) : d196679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d116753 q = 1) : d196657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46646 q ha hb
    | true =>
      simp only [d22341, d196657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d116753 q = 1) : d196658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d196658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d116753 q = 1) : d196661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46638 q ha hb
    | true =>
      simp only [d22266, d196661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d116753 q = 1) : d196662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d196662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d116753 q = 1) : d196663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d196663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d116753 q = 1) : d196664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d196664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d116753 q = 1) : d196665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d196665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22452 q = 1) (hb : d116753 q = 1) : d196679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22452, d196679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22452, d196679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46673 (p : Pattern) (ha : d22458 p = 1) (hb : d116753 p = 1) : d196754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d116753 q = 1) : d196728 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d196728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46664 q ha hb
    | true =>
      simp only [d22428, d196728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d116753 q = 1) : d196729 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d196729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d196729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d116753 q = 1) : d196730 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d196730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d196730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d116753 q = 1) : d196731 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d196731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d196731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d116753 q = 1) : d196732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d196732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d196732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22458 q = 1) (hb : d116753 q = 1) : d196754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22458, d196754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22458, d196754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46674 (p : Pattern) (ha : d116753 p = 1) (hb : d150206 p = 1) : d196760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d116753 q = 1) : d196694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d196694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46656 q ha hb
    | true =>
      simp only [d22299, d196694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46657 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d116753 q = 1) : d196695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d196695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d196695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d116753 q = 1) : d196696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d196696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d196696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d116753 q = 1) : d196697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d196697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d196697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d116753 q = 1) : d196704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d196704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46658 q ha hb
    | true =>
      simp only [d22309, d196704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46659 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d116753 q = 1) : d196705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d196705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d196705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d116753 q = 1) : d196706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d196706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d196706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d116753 q = 1) : d196720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d196720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46662 q ha hb
    | true =>
      simp only [d22351, d196720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46647 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150197 q = 1) : d196721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d196721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150197, d196721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d116753 q = 1) : d196734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d196734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46665 q ha hb
    | true =>
      simp only [d22434, d196734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d116753 q = 1) : d196735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d196735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d196735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150198 q = 1) : d196736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d196736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d196736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150199 q = 1) : d196737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d196737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150199, d196737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150200 q = 1) : d196738 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d196738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150200, d196738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22442 q = 1) (hb : d116753 q = 1) : d196742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22442, d196742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46667 q ha hb
    | true =>
      simp only [d22442, d196742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46668 q ha hb
  have h16 (q : Pattern) (ha : d22443 q = 1) (hb : d116753 q = 1) : d196743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22443, d196743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22443, d196743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22444 q = 1) (hb : d116753 q = 1) : d196744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22444, d196744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22444, d196744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22445 q = 1) (hb : d116753 q = 1) : d196745 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22445, d196745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22445, d196745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22448 q = 1) (hb : d116753 q = 1) : d196748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22448, d196748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46669 q ha hb
    | true =>
      simp only [d22448, d196748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46670 q ha hb
  have h20 (q : Pattern) (ha : d22449 q = 1) (hb : d116753 q = 1) : d196749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22449, d196749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22449, d196749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22450 q = 1) (hb : d116753 q = 1) : d196750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22450, d196750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22450, d196750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22453 q = 1) (hb : d116753 q = 1) : d196752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d196752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46671 q ha hb
    | true =>
      simp only [d22453, d196752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46672 q ha hb
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150202 q = 1) : d196753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d196753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150202, d196753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d22459 q = 1) (hb : d116753 q = 1) : d196755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d196755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46673 q ha hb
    | true =>
      simp only [d22459, d196755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22460 q = 1) (hb : d116753 q = 1) : d196756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d196756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22460, d196756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116753 q = 1) (hb : d150203 q = 1) : d196757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d196757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150203, d196757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116753 q = 1) (hb : d150204 q = 1) : d196758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d196758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150204, d196758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116753 q = 1) (hb : d150205 q = 1) : d196759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d196759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150205, d196759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116753 q = 1) (hb : d150206 q = 1) : d196760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d196760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150206, d196760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro46675 (p : Pattern) (ha : d116753 p = 1) (hb : d150213 p = 1) : d196780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22453 q = 1) (hb : d116753 q = 1) : d196752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22453, d196752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46671 q ha hb
    | true =>
      simp only [d22453, d196752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46672 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150202 q = 1) : d196753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d196753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150202, d196753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22459 q = 1) (hb : d116753 q = 1) : d196755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22459, d196755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46673 q ha hb
    | true =>
      simp only [d22459, d196755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22460 q = 1) (hb : d116753 q = 1) : d196756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22460, d196756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22460, d196756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150203 q = 1) : d196757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d196757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150203, d196757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150211 q = 1) : d196778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d196778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150211, d196778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150212 q = 1) : d196779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d196779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150212, d196779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150213 q = 1) : d196780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d196780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150213, d196780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46676 (p : Pattern) (ha : d22507 p = 1) (hb : d116752 p = 1) : d196788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22501 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22506 q = 1) (hb : d116750 q = 1) : d22506 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22507 q = 1) (hb : d116752 q = 1) : d196788 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22507, d116752, d196788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22507, d116752, d196788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46677 (p : Pattern) (ha : d22514 p = 1) (hb : d116752 p = 1) : d196789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22512 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22513 q = 1) (hb : d116750 q = 1) : d22513 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22514 q = 1) (hb : d116752 q = 1) : d196789 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22514, d116752, d196789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22514, d116752, d196789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46678 (p : Pattern) (ha : d22549 p = 1) (hb : d116753 p = 1) : d196800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22515 q = 1) (hb : d116752 q = 1) : d196790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22515, d196790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46676 q ha hb
    | true =>
      simp only [d22515, d196790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46677 q ha hb
  have h2 (q : Pattern) (ha : d22516 q = 1) (hb : d116752 q = 1) : d196791 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22516, d196791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22516, d196791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22517 q = 1) (hb : d116752 q = 1) : d196792 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22517, d196792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22517, d196792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22527 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22528 q = 1) (hb : d116753 q = 1) : d196793 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22528, d116753, d196793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22528, d116753, d196793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22535 q = 1) (hb : d116752 q = 1) : d196795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46677 q ha hb
    | true =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
  have h7 (q : Pattern) (ha : d22536 q = 1) (hb : d116752 q = 1) : d196796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22537 q = 1) (hb : d116752 q = 1) : d196797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22546 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22547 q = 1) (hb : d116753 q = 1) : d196798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d22548 q = 1) (hb : d116753 q = 1) : d196799 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22548, d196799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22548, d196799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22549 q = 1) (hb : d116753 q = 1) : d196800 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22549, d196800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22549, d196800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46679 (p : Pattern) (ha : d22543 p = 1) (hb : d116752 p = 1) : d196803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22542 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15416 q = 1) (hb : d116750 q = 1) : d15416 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22543 q = 1) (hb : d116752 q = 1) : d196803 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22543, d116752, d196803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22543, d116752, d196803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46680 (p : Pattern) (ha : d22554 p = 1) (hb : d116753 p = 1) : d196809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d116752 q = 1) : d196795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46677 q ha hb
    | true =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d116752 q = 1) : d196796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d116752 q = 1) : d196797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22546 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22547 q = 1) (hb : d116753 q = 1) : d196798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22544 q = 1) (hb : d116752 q = 1) : d196804 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d196804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
    | true =>
      simp only [d22544, d196804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46679 q ha hb
  have h7 (q : Pattern) (ha : d22545 q = 1) (hb : d116752 q = 1) : d196805 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d196805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d196805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22546 q = 1) (hb : d116752 q = 1) : d196806 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d196806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d196806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22552 q = 1) (hb : d116753 q = 1) : d196807 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22552, d116753, d196807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22552, d116753, d196807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22553 q = 1) (hb : d116753 q = 1) : d196808 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22553, d196808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22553, d196808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22554 q = 1) (hb : d116753 q = 1) : d196809 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22554, d196809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22554, d196809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46681 (p : Pattern) (ha : d22560 p = 1) (hb : d116753 p = 1) : d196815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22550 q = 1) (hb : d116753 q = 1) : d196801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22550, d196801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46678 q ha hb
    | true =>
      simp only [d22550, d196801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22551 q = 1) (hb : d116753 q = 1) : d196802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22551, d196802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22551, d196802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22555 q = 1) (hb : d116753 q = 1) : d196810 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d196810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46680 q ha hb
    | true =>
      simp only [d22555, d196810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22556 q = 1) (hb : d116753 q = 1) : d196811 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d196811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d196811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22557 q = 1) (hb : d116753 q = 1) : d196812 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22557, d196812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22557, d196812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22558 q = 1) (hb : d116753 q = 1) : d196813 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22558, d196813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22558, d196813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22559 q = 1) (hb : d116753 q = 1) : d196814 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22559, d196814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22559, d196814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22560 q = 1) (hb : d116753 q = 1) : d196815 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22560, d196815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22560, d196815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46682 (p : Pattern) (ha : d22574 p = 1) (hb : d116753 p = 1) : d196823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22555 q = 1) (hb : d116753 q = 1) : d196810 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22555, d196810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46680 q ha hb
    | true =>
      simp only [d22555, d196810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22556 q = 1) (hb : d116753 q = 1) : d196811 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22556, d196811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22556, d196811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d116753 q = 1) : d196818 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d196818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46653 q ha hb
    | true =>
      simp only [d22569, d196818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d116753 q = 1) : d196819 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d196819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d196819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22571 q = 1) (hb : d116753 q = 1) : d196820 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22571, d196820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22571, d196820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22572 q = 1) (hb : d116753 q = 1) : d196821 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22572, d196821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22572, d196821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22573 q = 1) (hb : d116753 q = 1) : d196822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22573, d196822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22573, d196822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22574 q = 1) (hb : d116753 q = 1) : d196823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22574, d196823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22574, d196823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46683 (p : Pattern) (ha : d22639 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22561 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22639 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22639, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22639, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46684 (p : Pattern) (ha : d22645 p = 1) (hb : d116753 p = 1) : d196831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d116752 q = 1) : d196795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46677 q ha hb
    | true =>
      simp only [d22535, d196795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d116752 q = 1) : d196796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d196796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d116752 q = 1) : d196797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d196797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22546 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22547 q = 1) (hb : d116753 q = 1) : d196798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d116753, d196798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22640 q = 1) (hb : d116752 q = 1) : d196826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22640, d196826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46651 q ha hb
    | true =>
      simp only [d22640, d196826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46683 q ha hb
  have h7 (q : Pattern) (ha : d22641 q = 1) (hb : d116752 q = 1) : d196827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22641, d196827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22641, d196827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22642 q = 1) (hb : d116752 q = 1) : d196828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22642, d196828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22642, d196828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22643 q = 1) (hb : d116753 q = 1) : d196829 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22643, d116753, d196829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22643, d116753, d196829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22644 q = 1) (hb : d116753 q = 1) : d196830 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22644, d196830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22644, d196830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22645 q = 1) (hb : d116753 q = 1) : d196831 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22645, d196831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22645, d196831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46685 (p : Pattern) (ha : d22651 p = 1) (hb : d116753 p = 1) : d196837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22646 q = 1) (hb : d116753 q = 1) : d196832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22646, d196832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46684 q ha hb
    | true =>
      simp only [d22646, d196832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22647 q = 1) (hb : d116753 q = 1) : d196833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22647, d196833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22647, d196833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22648 q = 1) (hb : d116753 q = 1) : d196834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22648, d196834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22648, d196834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22649 q = 1) (hb : d116753 q = 1) : d196835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22649, d196835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22649, d196835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22650 q = 1) (hb : d116753 q = 1) : d196836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22650, d196836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22650, d196836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22651 q = 1) (hb : d116753 q = 1) : d196837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22651, d196837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22651, d196837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46686 (p : Pattern) (ha : d116753 p = 1) (hb : d150223 p = 1) : d196843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22575 q = 1) (hb : d116753 q = 1) : d196824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22575, d196824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46681 q ha hb
    | true =>
      simp only [d22575, d196824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46682 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150219 q = 1) : d196825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d196825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150219, d196825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22652 q = 1) (hb : d116753 q = 1) : d196838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22652, d196838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46685 q ha hb
    | true =>
      simp only [d22652, d196838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22653 q = 1) (hb : d116753 q = 1) : d196839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22653, d196839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22653, d196839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150220 q = 1) : d196840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d196840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150220, d196840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150221 q = 1) : d196841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d196841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150221, d196841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150222 q = 1) : d196842 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d196842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150222, d196842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150223 q = 1) : d196843 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d196843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150223, d196843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46687 (p : Pattern) (ha : d116753 p = 1) (hb : d150229 p = 1) : d196860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22282 q = 1) (hb : d116753 q = 1) : d196677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22282, d196677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22282, d196677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46641 q ha hb
  have h2 (q : Pattern) (ha : d22283 q = 1) (hb : d116753 q = 1) : d196678 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22283, d196678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22283, d196678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22292 q = 1) (hb : d116753 q = 1) : d196687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d196687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46641 q ha hb
    | true =>
      simp only [d22292, d196687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46644 q ha hb
  have h4 (q : Pattern) (ha : d22293 q = 1) (hb : d116753 q = 1) : d196688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d196688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22293, d196688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22294 q = 1) (hb : d116753 q = 1) : d196689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22294, d196689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22294, d196689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150207 q = 1) : d196761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d196761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46666 q ha hb
    | true =>
      simp only [d150207, d196761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46674 q ha hb
  have h7 (q : Pattern) (ha : d22483 q = 1) (hb : d116753 q = 1) : d196774 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22483, d196774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46648 q ha hb
    | true =>
      simp only [d22483, d196774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46649 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150208 q = 1) : d196775 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d196775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150208, d196775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150209 q = 1) : d196776 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d196776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150209, d196776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150210 q = 1) : d196777 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d196777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150210, d196777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150214 q = 1) : d196781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d196781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150214, d196781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46675 q ha hb
  have h12 (q : Pattern) (ha : d22492 q = 1) (hb : d116753 q = 1) : d196783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22492, d196783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22492, d196783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46650 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150215 q = 1) : d196784 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d196784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150215, d196784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150216 q = 1) : d196785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d196785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150216, d196785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150217 q = 1) : d196786 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d196786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150217, d196786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150218 q = 1) : d196787 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d196787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150218, d196787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116753 q = 1) (hb : d150224 q = 1) : d196844 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d196844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150224, d196844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46686 q ha hb
  have h18 (q : Pattern) (ha : d22669 q = 1) (hb : d116753 q = 1) : d196855 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22669, d196855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22669, d196855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46655 q ha hb
  have h19 (q : Pattern) (ha : d116753 q = 1) (hb : d150225 q = 1) : d196856 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d196856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150225, d196856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116753 q = 1) (hb : d150226 q = 1) : d196857 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d196857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150226, d196857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116753 q = 1) (hb : d150227 q = 1) : d196858 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d196858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150227, d196858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116753 q = 1) (hb : d150228 q = 1) : d196859 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d196859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150228, d196859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150229 q = 1) : d196860 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d196860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150229, d196860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46688 (p : Pattern) (ha : d116753 p = 1) (hb : d150235 p = 1) : d196866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150230 q = 1) : d196861 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d196861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150230, d196861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46687 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150231 q = 1) : d196862 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d196862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150231, d196862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150232 q = 1) : d196863 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d196863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150232, d196863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150233 q = 1) : d196864 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d196864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150233, d196864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150234 q = 1) : d196865 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d196865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150234, d196865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150235 q = 1) : d196866 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d196866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150235, d196866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46689 (p : Pattern) (ha : d22686 p = 1) (hb : d116752 p = 1) : d196871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22685 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13682 q = 1) (hb : d116750 q = 1) : d13682 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22686 q = 1) (hb : d116752 q = 1) : d196871 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22686, d116752, d196871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22686, d116752, d196871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46690 (p : Pattern) (ha : d22694 p = 1) (hb : d116752 p = 1) : d196872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22692 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22693 q = 1) (hb : d116750 q = 1) : d22693 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22694 q = 1) (hb : d116752 q = 1) : d196872 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22694, d116752, d196872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22694, d116752, d196872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46691 (p : Pattern) (ha : d22710 p = 1) (hb : d116752 p = 1) : d196877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22709 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15557 q = 1) (hb : d116750 q = 1) : d15557 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22710 q = 1) (hb : d116752 q = 1) : d196877 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22710, d116752, d196877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22710, d116752, d196877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46692 (p : Pattern) (ha : d22716 p = 1) (hb : d116753 p = 1) : d196883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d116752 q = 1) : d196873 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46689 q ha hb
    | true =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d116752 q = 1) : d196874 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d116752 q = 1) : d196875 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22707 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22708 q = 1) (hb : d116753 q = 1) : d196876 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22711 q = 1) (hb : d116752 q = 1) : d196878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d196878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
    | true =>
      simp only [d22711, d196878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46691 q ha hb
  have h7 (q : Pattern) (ha : d22712 q = 1) (hb : d116752 q = 1) : d196879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d196879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d196879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22713 q = 1) (hb : d116752 q = 1) : d196880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d196880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d196880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22714 q = 1) (hb : d116753 q = 1) : d196881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d116753, d196881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22714, d116753, d196881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22715 q = 1) (hb : d116753 q = 1) : d196882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22715, d196882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22715, d196882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22716 q = 1) (hb : d116753 q = 1) : d196883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22716, d196883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22716, d196883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46693 (p : Pattern) (ha : d22720 p = 1) (hb : d116753 p = 1) : d196887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22711 q = 1) (hb : d116752 q = 1) : d196878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22711, d196878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
    | true =>
      simp only [d22711, d196878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46691 q ha hb
  have h2 (q : Pattern) (ha : d22712 q = 1) (hb : d116752 q = 1) : d196879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22712, d196879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22712, d196879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22713 q = 1) (hb : d116752 q = 1) : d196880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22713, d196880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22713, d196880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22714 q = 1) (hb : d116753 q = 1) : d196881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22714, d116753, d196881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22714, d116753, d196881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22719 q = 1) (hb : d116753 q = 1) : d196886 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22719, d196886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22719, d196886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22720 q = 1) (hb : d116753 q = 1) : d196887 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22720, d196887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22720, d196887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46694 (p : Pattern) (ha : d22726 p = 1) (hb : d116753 p = 1) : d196893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46692 q ha hb
    | true =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d116753 q = 1) : d196891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d116753 q = 1) : d196892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22726 q = 1) (hb : d116753 q = 1) : d196893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22726, d196893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22726, d196893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46695 (p : Pattern) (ha : d22730 p = 1) (hb : d116753 p = 1) : d196897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d116753 q = 1) : d196894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d116753 q = 1) : d196895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d116753 q = 1) : d196896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d196896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d196896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22730 q = 1) (hb : d116753 q = 1) : d196897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22730, d196897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22730, d196897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46696 (p : Pattern) (ha : d22736 p = 1) (hb : d116753 p = 1) : d196903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d116753 q = 1) : d196898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d196898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46694 q ha hb
    | true =>
      simp only [d22731, d196898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46695 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d116753 q = 1) : d196899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d196899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d196899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d116753 q = 1) : d196900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d196900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d196900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d116753 q = 1) : d196901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d196901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d196901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d116753 q = 1) : d196902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d196902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d196902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22736 q = 1) (hb : d116753 q = 1) : d196903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d196903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d196903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46697 (p : Pattern) (ha : d22739 p = 1) (hb : d116753 p = 1) : d196906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46692 q ha hb
    | true =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d116753 q = 1) : d196891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22725 q = 1) (hb : d116753 q = 1) : d196892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22725, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22725, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22739 q = 1) (hb : d116753 q = 1) : d196906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22739, d196906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22739, d196906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46698 (p : Pattern) (ha : d22740 p = 1) (hb : d116753 p = 1) : d196907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d116753 q = 1) : d196894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d116753 q = 1) : d196895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22729 q = 1) (hb : d116753 q = 1) : d196896 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22729, d196896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22729, d196896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22740 q = 1) (hb : d116753 q = 1) : d196907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22740, d196907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22740, d196907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46699 (p : Pattern) (ha : d22746 p = 1) (hb : d116753 p = 1) : d196913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22731 q = 1) (hb : d116753 q = 1) : d196898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d196898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46694 q ha hb
    | true =>
      simp only [d22731, d196898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46695 q ha hb
  have h2 (q : Pattern) (ha : d22732 q = 1) (hb : d116753 q = 1) : d196899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d196899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22732, d196899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22733 q = 1) (hb : d116753 q = 1) : d196900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d196900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22733, d196900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22734 q = 1) (hb : d116753 q = 1) : d196901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d196901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22734, d196901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22735 q = 1) (hb : d116753 q = 1) : d196902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d196902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d196902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22741 q = 1) (hb : d116753 q = 1) : d196908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d196908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46697 q ha hb
    | true =>
      simp only [d22741, d196908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46698 q ha hb
  have h7 (q : Pattern) (ha : d22742 q = 1) (hb : d116753 q = 1) : d196909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d196909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d196909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22743 q = 1) (hb : d116753 q = 1) : d196910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d196910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22743, d196910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22744 q = 1) (hb : d116753 q = 1) : d196911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d196911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d196911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22745 q = 1) (hb : d116753 q = 1) : d196912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d196912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d196912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22746 q = 1) (hb : d116753 q = 1) : d196913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d196913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22746, d196913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46700 (p : Pattern) (ha : d22704 p = 1) (hb : d116752 p = 1) : d196877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22703 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15557 q = 1) (hb : d116750 q = 1) : d15557 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22704 q = 1) (hb : d116752 q = 1) : d196877 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22704, d116752, d196877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22704, d116752, d196877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46701 (p : Pattern) (ha : d22783 p = 1) (hb : d116753 p = 1) : d196883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d116752 q = 1) : d196873 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46689 q ha hb
    | true =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d116752 q = 1) : d196874 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d116752 q = 1) : d196875 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22707 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22708 q = 1) (hb : d116753 q = 1) : d196876 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22705 q = 1) (hb : d116752 q = 1) : d196878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22705, d196878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
    | true =>
      simp only [d22705, d196878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46700 q ha hb
  have h7 (q : Pattern) (ha : d22706 q = 1) (hb : d116752 q = 1) : d196879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22706, d196879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22706, d196879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22707 q = 1) (hb : d116752 q = 1) : d196880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22707, d196880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22707, d196880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22781 q = 1) (hb : d116753 q = 1) : d196881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22781, d116753, d196881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22781, d116753, d196881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22782 q = 1) (hb : d116753 q = 1) : d196882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22782, d196882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22782, d196882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22783 q = 1) (hb : d116753 q = 1) : d196883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22783, d196883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22783, d196883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46702 (p : Pattern) (ha : d22793 p = 1) (hb : d116753 p = 1) : d196893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46701 q ha hb
    | true =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d116753 q = 1) : d196891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d116753 q = 1) : d196892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22793 q = 1) (hb : d116753 q = 1) : d196893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22793, d196893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22793, d196893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46703 (p : Pattern) (ha : d22909 p = 1) (hb : d116753 p = 1) : d196994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22899 q = 1) (hb : d116753 q = 1) : d196898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22899, d196898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46702 q ha hb
    | true =>
      simp only [d22899, d196898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46695 q ha hb
  have h2 (q : Pattern) (ha : d22900 q = 1) (hb : d116753 q = 1) : d196899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22900, d196899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22900, d196899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22901 q = 1) (hb : d116753 q = 1) : d196900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22901, d196900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22901, d196900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22902 q = 1) (hb : d116753 q = 1) : d196901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22902, d196901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22902, d196901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22903 q = 1) (hb : d116753 q = 1) : d196902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22903, d196902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22903, d196902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22904 q = 1) (hb : d116753 q = 1) : d196989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d196989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46695 q ha hb
    | true =>
      simp only [d22904, d196989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22905 q = 1) (hb : d116753 q = 1) : d196990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d196990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d196990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22906 q = 1) (hb : d116753 q = 1) : d196991 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d196991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22906, d196991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22907 q = 1) (hb : d116753 q = 1) : d196992 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d196992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d196992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22908 q = 1) (hb : d116753 q = 1) : d196993 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d196993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d196993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22909 q = 1) (hb : d116753 q = 1) : d196994 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22909, d196994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22909, d196994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46704 (p : Pattern) (ha : d22915 p = 1) (hb : d116753 p = 1) : d197000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22904 q = 1) (hb : d116753 q = 1) : d196989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22904, d196989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46695 q ha hb
    | true =>
      simp only [d22904, d196989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22905 q = 1) (hb : d116753 q = 1) : d196990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22905, d196990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22905, d196990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22906 q = 1) (hb : d116753 q = 1) : d196991 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22906, d196991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22906, d196991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22907 q = 1) (hb : d116753 q = 1) : d196992 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22907, d196992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22907, d196992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22908 q = 1) (hb : d116753 q = 1) : d196993 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22908, d196993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22908, d196993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22910 q = 1) (hb : d116753 q = 1) : d196995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d196995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46698 q ha hb
    | true =>
      simp only [d22910, d196995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22911 q = 1) (hb : d116753 q = 1) : d196996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d196996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d196996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22912 q = 1) (hb : d116753 q = 1) : d196997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d196997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22912, d196997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22913 q = 1) (hb : d116753 q = 1) : d196998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d196998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d196998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22914 q = 1) (hb : d116753 q = 1) : d196999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d196999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d196999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22915 q = 1) (hb : d116753 q = 1) : d197000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22915, d197000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22915, d197000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46705 (p : Pattern) (ha : d22924 p = 1) (hb : d116753 p = 1) : d197009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22910 q = 1) (hb : d116753 q = 1) : d196995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22910, d196995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46698 q ha hb
    | true =>
      simp only [d22910, d196995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22911 q = 1) (hb : d116753 q = 1) : d196996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22911, d196996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22911, d196996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22912 q = 1) (hb : d116753 q = 1) : d196997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22912, d196997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22912, d196997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22913 q = 1) (hb : d116753 q = 1) : d196998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22913, d196998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22913, d196998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22914 q = 1) (hb : d116753 q = 1) : d196999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22914, d196999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22914, d196999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22924 q = 1) (hb : d116753 q = 1) : d197009 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22924, d197009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22924, d197009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46706 (p : Pattern) (ha : d22948 p = 1) (hb : d116752 p = 1) : d197021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22947 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22937 q = 1) (hb : d116750 q = 1) : d22937 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22948 q = 1) (hb : d116752 q = 1) : d197021 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22948, d116752, d197021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22948, d116752, d197021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46707 (p : Pattern) (ha : d22976 p = 1) (hb : d116752 p = 1) : d197030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15794 q = 1) (hb : d116750 q = 1) : d15794 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22976 q = 1) (hb : d116752 q = 1) : d197030 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22976, d116752, d197030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22976, d116752, d197030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46708 (p : Pattern) (ha : d22982 p = 1) (hb : d116753 p = 1) : d197044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22977 q = 1) (hb : d116752 q = 1) : d197031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d197031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
    | true =>
      simp only [d22977, d197031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46707 q ha hb
  have h2 (q : Pattern) (ha : d22978 q = 1) (hb : d116752 q = 1) : d197032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d197032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d197032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22979 q = 1) (hb : d116752 q = 1) : d197033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d197033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d197033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22980 q = 1) (hb : d116753 q = 1) : d197034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d116753, d197034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22980, d116753, d197034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22981 q = 1) (hb : d116753 q = 1) : d197043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22981, d197043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22981, d197043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22982 q = 1) (hb : d116753 q = 1) : d197044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22982, d197044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22982, d197044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46709 (p : Pattern) (ha : d23068 p = 1) (hb : d116753 p = 1) : d197075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22983 q = 1) (hb : d116753 q = 1) : d197045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d197045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46708 q ha hb
    | true =>
      simp only [d22983, d197045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22984 q = 1) (hb : d116753 q = 1) : d197046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d197046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d197046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23065 q = 1) (hb : d116753 q = 1) : d197072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23065, d197072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23065, d197072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23066 q = 1) (hb : d116753 q = 1) : d197073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23066, d197073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23066, d197073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23067 q = 1) (hb : d116753 q = 1) : d197074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23067, d197074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23067, d197074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23068 q = 1) (hb : d116753 q = 1) : d197075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23068, d197075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23068, d197075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46710 (p : Pattern) (ha : d23074 p = 1) (hb : d116753 p = 1) : d197081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23069 q = 1) (hb : d116753 q = 1) : d197076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23069, d197076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46709 q ha hb
    | true =>
      simp only [d23069, d197076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23070 q = 1) (hb : d116753 q = 1) : d197077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23070, d197077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23070, d197077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23071 q = 1) (hb : d116753 q = 1) : d197078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23071, d197078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23071, d197078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23072 q = 1) (hb : d116753 q = 1) : d197079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23072, d197079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23072, d197079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23073 q = 1) (hb : d116753 q = 1) : d197080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23073, d197080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23073, d197080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23074 q = 1) (hb : d116753 q = 1) : d197081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23074, d197081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23074, d197081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46711 (p : Pattern) (ha : d22751 p = 1) (hb : d116753 p = 1) : d196918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46692 q ha hb
    | true =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d116753 q = 1) : d196891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d116753 q = 1) : d196917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d196917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d196917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22751 q = 1) (hb : d116753 q = 1) : d196918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22751, d196918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22751, d196918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46712 (p : Pattern) (ha : d22753 p = 1) (hb : d116753 p = 1) : d196920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d116753 q = 1) : d196894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d116753 q = 1) : d196895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d116753 q = 1) : d196919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d196919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d196919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22753 q = 1) (hb : d116753 q = 1) : d196920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22753, d196920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22753, d196920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46713 (p : Pattern) (ha : d22760 p = 1) (hb : d116753 p = 1) : d196927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46692 q ha hb
    | true =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d116753 q = 1) : d196925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d196925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d196925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d116753 q = 1) : d196926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d196926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d196926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22760 q = 1) (hb : d116753 q = 1) : d196927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22760, d196927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22760, d196927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46714 (p : Pattern) (ha : d22763 p = 1) (hb : d116753 p = 1) : d196930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d116753 q = 1) : d196894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d116753 q = 1) : d196928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d196928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d196928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d116753 q = 1) : d196929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d196929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d196929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22763 q = 1) (hb : d116753 q = 1) : d196930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22763, d196930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22763, d196930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46715 (p : Pattern) (ha : d22768 p = 1) (hb : d116752 p = 1) : d196934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17228 q = 1) (hb : d116750 q = 1) : d17228 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22768 q = 1) (hb : d116752 q = 1) : d196934 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22768, d116752, d196934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22768, d116752, d196934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46716 (p : Pattern) (ha : d22778 p = 1) (hb : d116753 p = 1) : d196940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22769 q = 1) (hb : d116752 q = 1) : d196935 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22769, d196935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46715 q ha hb
    | true =>
      simp only [d22769, d196935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46689 q ha hb
  have h2 (q : Pattern) (ha : d22770 q = 1) (hb : d116752 q = 1) : d196936 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22770, d196936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22770, d196936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22771 q = 1) (hb : d116752 q = 1) : d196937 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22771, d196937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22771, d196937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22775 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22776 q = 1) (hb : d116753 q = 1) : d196938 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22776, d116753, d196938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22776, d116753, d196938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22695 q = 1) (hb : d116752 q = 1) : d196873 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46689 q ha hb
    | true =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
  have h7 (q : Pattern) (ha : d22696 q = 1) (hb : d116752 q = 1) : d196874 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22697 q = 1) (hb : d116752 q = 1) : d196875 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22707 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22708 q = 1) (hb : d116753 q = 1) : d196876 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d22777 q = 1) (hb : d116753 q = 1) : d196939 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22777, d196939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22777, d196939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22778 q = 1) (hb : d116753 q = 1) : d196940 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22778, d196940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22778, d196940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46717 (p : Pattern) (ha : d22789 p = 1) (hb : d116753 p = 1) : d196946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d116753 q = 1) : d196941 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46716 q ha hb
    | true =>
      simp only [d22779, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d116753 q = 1) : d196942 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46701 q ha hb
    | true =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d116753 q = 1) : d196943 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d196943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d196943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d116753 q = 1) : d196944 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d196944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d196944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d116753 q = 1) : d196945 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d196945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d196945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22789 q = 1) (hb : d116753 q = 1) : d196946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22789, d196946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22789, d196946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46718 (p : Pattern) (ha : d22854 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22709 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22854 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22854, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22854, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46719 (p : Pattern) (ha : d22860 p = 1) (hb : d116753 p = 1) : d196954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22695 q = 1) (hb : d116752 q = 1) : d196873 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46689 q ha hb
    | true =>
      simp only [d22695, d196873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
  have h2 (q : Pattern) (ha : d22696 q = 1) (hb : d116752 q = 1) : d196874 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22696, d196874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22697 q = 1) (hb : d116752 q = 1) : d196875 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22697, d196875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22707 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22708 q = 1) (hb : d116753 q = 1) : d196876 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22708, d116753, d196876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22855 q = 1) (hb : d116752 q = 1) : d196949 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22855, d196949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46690 q ha hb
    | true =>
      simp only [d22855, d196949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46718 q ha hb
  have h7 (q : Pattern) (ha : d22856 q = 1) (hb : d116752 q = 1) : d196950 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22856, d196950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22856, d196950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22857 q = 1) (hb : d116752 q = 1) : d196951 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22857, d196951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22857, d196951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22858 q = 1) (hb : d116753 q = 1) : d196952 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22858, d116753, d196952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22858, d116753, d196952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22859 q = 1) (hb : d116753 q = 1) : d196953 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22859, d196953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22859, d196953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22860 q = 1) (hb : d116753 q = 1) : d196954 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22860, d196954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22860, d196954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46720 (p : Pattern) (ha : d22866 p = 1) (hb : d116753 p = 1) : d196960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d116753 q = 1) : d196955 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d196955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46719 q ha hb
    | true =>
      simp only [d22861, d196955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d116753 q = 1) : d196956 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d196956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d196956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d116753 q = 1) : d196957 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d196957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d196957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d116753 q = 1) : d196958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d196958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d196958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d116753 q = 1) : d196959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d196959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d196959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22866 q = 1) (hb : d116753 q = 1) : d196960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22866, d196960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22866, d196960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46721 (p : Pattern) (ha : d116753 p = 1) (hb : d150244 p = 1) : d196966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d116753 q = 1) : d196921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d196921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46711 q ha hb
    | true =>
      simp only [d22754, d196921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46712 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d116753 q = 1) : d196922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d196922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d196922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d116753 q = 1) : d196923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d196923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d196923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d116753 q = 1) : d196924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d196924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d196924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d116753 q = 1) : d196931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d196931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46713 q ha hb
    | true =>
      simp only [d22764, d196931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46714 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d116753 q = 1) : d196932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d196932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d196932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d116753 q = 1) : d196933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d196933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d196933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d116753 q = 1) : d196947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d196947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46717 q ha hb
    | true =>
      simp only [d22794, d196947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46702 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150240 q = 1) : d196948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d196948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150240, d196948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d116753 q = 1) : d196961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d196961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46720 q ha hb
    | true =>
      simp only [d22867, d196961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d116753 q = 1) : d196962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d196962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d196962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150241 q = 1) : d196963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d196963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d196963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150242 q = 1) : d196964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d196964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150242, d196964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150243 q = 1) : d196965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d196965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150243, d196965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150244 q = 1) : d196966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d196966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150244, d196966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46722 (p : Pattern) (ha : d22873 p = 1) (hb : d116753 p = 1) : d196967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46692 q ha hb
    | true =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22724 q = 1) (hb : d116753 q = 1) : d196891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22724, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22750 q = 1) (hb : d116753 q = 1) : d196917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22750, d196917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22750, d196917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22873 q = 1) (hb : d116753 q = 1) : d196967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22873, d196967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22873, d196967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46723 (p : Pattern) (ha : d22874 p = 1) (hb : d116753 p = 1) : d196968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d116753 q = 1) : d196894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22728 q = 1) (hb : d116753 q = 1) : d196895 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22728, d196895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22752 q = 1) (hb : d116753 q = 1) : d196919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22752, d196919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22752, d196919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22874 q = 1) (hb : d116753 q = 1) : d196968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22874, d196968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22874, d196968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46724 (p : Pattern) (ha : d22879 p = 1) (hb : d116753 p = 1) : d196973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22717 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46692 q ha hb
    | true =>
      simp only [d22717, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22718 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22718, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22723 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22723, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22758 q = 1) (hb : d116753 q = 1) : d196925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22758, d196925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22758, d196925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22759 q = 1) (hb : d116753 q = 1) : d196926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22759, d196926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22759, d196926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22879 q = 1) (hb : d116753 q = 1) : d196973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22879, d196973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22879, d196973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46725 (p : Pattern) (ha : d22880 p = 1) (hb : d116753 p = 1) : d196974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22727 q = 1) (hb : d116753 q = 1) : d196894 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22727, d196894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22761 q = 1) (hb : d116753 q = 1) : d196928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22761, d196928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22761, d196928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22762 q = 1) (hb : d116753 q = 1) : d196929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22762, d196929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22762, d196929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22880 q = 1) (hb : d116753 q = 1) : d196974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22880, d196974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22880, d196974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46726 (p : Pattern) (ha : d22884 p = 1) (hb : d116753 p = 1) : d196978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22779 q = 1) (hb : d116753 q = 1) : d196941 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22779, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46716 q ha hb
    | true =>
      simp only [d22779, d196941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22780 q = 1) (hb : d116753 q = 1) : d196942 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22780, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22780, d196942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22784 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46701 q ha hb
    | true =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22785 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22786 q = 1) (hb : d116753 q = 1) : d196943 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22786, d196943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22786, d196943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22787 q = 1) (hb : d116753 q = 1) : d196944 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22787, d196944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22787, d196944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22788 q = 1) (hb : d116753 q = 1) : d196945 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22788, d196945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22788, d196945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22884 q = 1) (hb : d116753 q = 1) : d196978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22884, d196978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22884, d196978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46727 (p : Pattern) (ha : d22885 p = 1) (hb : d116753 p = 1) : d196906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22784 q = 1) (hb : d116753 q = 1) : d196884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46701 q ha hb
    | true =>
      simp only [d22784, d196884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22785 q = 1) (hb : d116753 q = 1) : d196885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22785, d196885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22721 q = 1) (hb : d116753 q = 1) : d196888 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46693 q ha hb
    | true =>
      simp only [d22721, d196888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22722 q = 1) (hb : d116753 q = 1) : d196889 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22722, d196889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22790 q = 1) (hb : d116753 q = 1) : d196890 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22790, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22790, d196890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22791 q = 1) (hb : d116753 q = 1) : d196891 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22791, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22791, d196891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22792 q = 1) (hb : d116753 q = 1) : d196892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22792, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22792, d196892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22885 q = 1) (hb : d116753 q = 1) : d196906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22885, d196906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22885, d196906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46728 (p : Pattern) (ha : d22891 p = 1) (hb : d116753 p = 1) : d196981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22861 q = 1) (hb : d116753 q = 1) : d196955 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22861, d196955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46719 q ha hb
    | true =>
      simp only [d22861, d196955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22862 q = 1) (hb : d116753 q = 1) : d196956 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22862, d196956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22862, d196956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22863 q = 1) (hb : d116753 q = 1) : d196957 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22863, d196957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22863, d196957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22864 q = 1) (hb : d116753 q = 1) : d196958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22864, d196958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22864, d196958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22865 q = 1) (hb : d116753 q = 1) : d196959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22865, d196959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22865, d196959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22891 q = 1) (hb : d116753 q = 1) : d196981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22891, d196981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22891, d196981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46729 (p : Pattern) (ha : d116753 p = 1) (hb : d150249 p = 1) : d196987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22754 q = 1) (hb : d116753 q = 1) : d196921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22754, d196921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46711 q ha hb
    | true =>
      simp only [d22754, d196921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46712 q ha hb
  have h2 (q : Pattern) (ha : d22755 q = 1) (hb : d116753 q = 1) : d196922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22755, d196922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22755, d196922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22756 q = 1) (hb : d116753 q = 1) : d196923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22756, d196923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22756, d196923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22757 q = 1) (hb : d116753 q = 1) : d196924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22757, d196924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22757, d196924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22764 q = 1) (hb : d116753 q = 1) : d196931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22764, d196931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46713 q ha hb
    | true =>
      simp only [d22764, d196931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46714 q ha hb
  have h6 (q : Pattern) (ha : d22765 q = 1) (hb : d116753 q = 1) : d196932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22765, d196932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22765, d196932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22766 q = 1) (hb : d116753 q = 1) : d196933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22766, d196933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22766, d196933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22794 q = 1) (hb : d116753 q = 1) : d196947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22794, d196947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46717 q ha hb
    | true =>
      simp only [d22794, d196947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46702 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150240 q = 1) : d196948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d196948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150240, d196948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22867 q = 1) (hb : d116753 q = 1) : d196961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22867, d196961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46720 q ha hb
    | true =>
      simp only [d22867, d196961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22868 q = 1) (hb : d116753 q = 1) : d196962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22868, d196962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22868, d196962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150241 q = 1) : d196963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d196963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150241, d196963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150242 q = 1) : d196964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d196964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150242, d196964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150243 q = 1) : d196965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d196965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150243, d196965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22875 q = 1) (hb : d116753 q = 1) : d196969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22875, d196969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46722 q ha hb
    | true =>
      simp only [d22875, d196969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46723 q ha hb
  have h16 (q : Pattern) (ha : d22876 q = 1) (hb : d116753 q = 1) : d196970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22876, d196970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22876, d196970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22877 q = 1) (hb : d116753 q = 1) : d196971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22877, d196971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d22877, d196971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d22878 q = 1) (hb : d116753 q = 1) : d196972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22878, d196972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22878, d196972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22881 q = 1) (hb : d116753 q = 1) : d196975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22881, d196975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46724 q ha hb
    | true =>
      simp only [d22881, d196975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46725 q ha hb
  have h20 (q : Pattern) (ha : d22882 q = 1) (hb : d116753 q = 1) : d196976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22882, d196976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22882, d196976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d22883 q = 1) (hb : d116753 q = 1) : d196977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22883, d196977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d22883, d196977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d22886 q = 1) (hb : d116753 q = 1) : d196979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d196979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46726 q ha hb
    | true =>
      simp only [d22886, d196979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46727 q ha hb
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150245 q = 1) : d196980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d196980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150245, d196980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d22892 q = 1) (hb : d116753 q = 1) : d196982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d196982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46728 q ha hb
    | true =>
      simp only [d22892, d196982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d22893 q = 1) (hb : d116753 q = 1) : d196983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d196983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d22893, d196983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116753 q = 1) (hb : d150246 q = 1) : d196984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d196984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150246, d196984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116753 q = 1) (hb : d150247 q = 1) : d196985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150247, d196985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150247, d196985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116753 q = 1) (hb : d150248 q = 1) : d196986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150248, d196986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150248, d196986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116753 q = 1) (hb : d150249 q = 1) : d196987 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150249, d196987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150249, d196987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro46730 (p : Pattern) (ha : d116753 p = 1) (hb : d150256 p = 1) : d197007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22886 q = 1) (hb : d116753 q = 1) : d196979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22886, d196979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46726 q ha hb
    | true =>
      simp only [d22886, d196979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46727 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150245 q = 1) : d196980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d196980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150245, d196980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22892 q = 1) (hb : d116753 q = 1) : d196982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22892, d196982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46728 q ha hb
    | true =>
      simp only [d22892, d196982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22893 q = 1) (hb : d116753 q = 1) : d196983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22893, d196983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22893, d196983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150246 q = 1) : d196984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d196984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150246, d196984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150254 q = 1) : d197005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150254, d197005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150254, d197005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150255 q = 1) : d197006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150255, d197006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150255, d197006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150256 q = 1) : d197007 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d197007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150256, d197007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46731 (p : Pattern) (ha : d22931 p = 1) (hb : d116752 p = 1) : d197015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22930 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17374 q = 1) (hb : d116750 q = 1) : d17374 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22931 q = 1) (hb : d116752 q = 1) : d197015 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22931, d116752, d197015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22931, d116752, d197015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46732 (p : Pattern) (ha : d22933 p = 1) (hb : d116752 p = 1) : d197016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22932 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13821 q = 1) (hb : d116750 q = 1) : d13821 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22933 q = 1) (hb : d116752 q = 1) : d197016 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22933, d116752, d197016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22933, d116752, d197016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46733 (p : Pattern) (ha : d22963 p = 1) (hb : d116753 p = 1) : d197027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22934 q = 1) (hb : d116752 q = 1) : d197017 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22934, d197017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46731 q ha hb
    | true =>
      simp only [d22934, d197017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46732 q ha hb
  have h2 (q : Pattern) (ha : d22935 q = 1) (hb : d116752 q = 1) : d197018 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22935, d197018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22935, d197018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22936 q = 1) (hb : d116752 q = 1) : d197019 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22936, d197019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22936, d197019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22941 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22942 q = 1) (hb : d116753 q = 1) : d197020 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22942, d116753, d197020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22942, d116753, d197020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22949 q = 1) (hb : d116752 q = 1) : d197022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46732 q ha hb
    | true =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
  have h7 (q : Pattern) (ha : d22950 q = 1) (hb : d116752 q = 1) : d197023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22951 q = 1) (hb : d116752 q = 1) : d197024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22960 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22961 q = 1) (hb : d116753 q = 1) : d197025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d22962 q = 1) (hb : d116753 q = 1) : d197026 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22962, d197026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22962, d197026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22963 q = 1) (hb : d116753 q = 1) : d197027 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22963, d197027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22963, d197027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46734 (p : Pattern) (ha : d22957 p = 1) (hb : d116752 p = 1) : d197030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15794 q = 1) (hb : d116750 q = 1) : d15794 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22957 q = 1) (hb : d116752 q = 1) : d197030 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22957, d116752, d197030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d22957, d116752, d197030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46735 (p : Pattern) (ha : d22968 p = 1) (hb : d116753 p = 1) : d197036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d116752 q = 1) : d197022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46732 q ha hb
    | true =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d116752 q = 1) : d197023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d116752 q = 1) : d197024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22960 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22961 q = 1) (hb : d116753 q = 1) : d197025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d22958 q = 1) (hb : d116752 q = 1) : d197031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d197031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
    | true =>
      simp only [d22958, d197031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46734 q ha hb
  have h7 (q : Pattern) (ha : d22959 q = 1) (hb : d116752 q = 1) : d197032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d197032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d197032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22960 q = 1) (hb : d116752 q = 1) : d197033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d197033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d197033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22966 q = 1) (hb : d116753 q = 1) : d197034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22966, d116753, d197034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22966, d116753, d197034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22967 q = 1) (hb : d116753 q = 1) : d197035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22967, d197035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22967, d197035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22968 q = 1) (hb : d116753 q = 1) : d197036 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22968, d197036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22968, d197036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46736 (p : Pattern) (ha : d22974 p = 1) (hb : d116753 p = 1) : d197042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22964 q = 1) (hb : d116753 q = 1) : d197028 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22964, d197028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46733 q ha hb
    | true =>
      simp only [d22964, d197028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22965 q = 1) (hb : d116753 q = 1) : d197029 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22965, d197029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22965, d197029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22969 q = 1) (hb : d116753 q = 1) : d197037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d197037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46735 q ha hb
    | true =>
      simp only [d22969, d197037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22970 q = 1) (hb : d116753 q = 1) : d197038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d197038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d197038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22971 q = 1) (hb : d116753 q = 1) : d197039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22971, d197039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22971, d197039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22972 q = 1) (hb : d116753 q = 1) : d197040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22972, d197040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22972, d197040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22973 q = 1) (hb : d116753 q = 1) : d197041 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22973, d197041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22973, d197041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22974 q = 1) (hb : d116753 q = 1) : d197042 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22974, d197042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22974, d197042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46737 (p : Pattern) (ha : d22988 p = 1) (hb : d116753 p = 1) : d197050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22969 q = 1) (hb : d116753 q = 1) : d197037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d197037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46735 q ha hb
    | true =>
      simp only [d22969, d197037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22970 q = 1) (hb : d116753 q = 1) : d197038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d197038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d197038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d116753 q = 1) : d197045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d197045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46708 q ha hb
    | true =>
      simp only [d22983, d197045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d116753 q = 1) : d197046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d197046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d197046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22985 q = 1) (hb : d116753 q = 1) : d197047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22985, d197047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22985, d197047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22986 q = 1) (hb : d116753 q = 1) : d197048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22986, d197048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22986, d197048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22987 q = 1) (hb : d116753 q = 1) : d197049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22987, d197049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22987, d197049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22988 q = 1) (hb : d116753 q = 1) : d197050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22988, d197050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22988, d197050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46738 (p : Pattern) (ha : d23045 p = 1) (hb : d116752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23045 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23045, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d23045, d116752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46739 (p : Pattern) (ha : d23051 p = 1) (hb : d116753 p = 1) : d197058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d116752 q = 1) : d197022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46732 q ha hb
    | true =>
      simp only [d22949, d197022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d116752 q = 1) : d197023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d197023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d116752 q = 1) : d197024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d197024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22960 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22961 q = 1) (hb : d116753 q = 1) : d197025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d116753, d197025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d23046 q = 1) (hb : d116752 q = 1) : d197053 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23046, d197053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46706 q ha hb
    | true =>
      simp only [d23046, d197053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46738 q ha hb
  have h7 (q : Pattern) (ha : d23047 q = 1) (hb : d116752 q = 1) : d197054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23047, d197054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23047, d197054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23048 q = 1) (hb : d116752 q = 1) : d197055 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23048, d197055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23048, d197055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23049 q = 1) (hb : d116753 q = 1) : d197056 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23049, d116753, d197056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23049, d116753, d197056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23050 q = 1) (hb : d116753 q = 1) : d197057 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23050, d197057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23050, d197057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23051 q = 1) (hb : d116753 q = 1) : d197058 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23051, d197058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23051, d197058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46740 (p : Pattern) (ha : d23057 p = 1) (hb : d116753 p = 1) : d197064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23052 q = 1) (hb : d116753 q = 1) : d197059 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23052, d197059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46739 q ha hb
    | true =>
      simp only [d23052, d197059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23053 q = 1) (hb : d116753 q = 1) : d197060 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23053, d197060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23053, d197060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23054 q = 1) (hb : d116753 q = 1) : d197061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23054, d197061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23054, d197061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23055 q = 1) (hb : d116753 q = 1) : d197062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23055, d197062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23055, d197062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23056 q = 1) (hb : d116753 q = 1) : d197063 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23056, d197063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23056, d197063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23057 q = 1) (hb : d116753 q = 1) : d197064 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23057, d197064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23057, d197064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46741 (p : Pattern) (ha : d116753 p = 1) (hb : d150266 p = 1) : d197070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22989 q = 1) (hb : d116753 q = 1) : d197051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22989, d197051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46736 q ha hb
    | true =>
      simp only [d22989, d197051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46737 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150262 q = 1) : d197052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150262, d197052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150262, d197052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d23058 q = 1) (hb : d116753 q = 1) : d197065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23058, d197065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46740 q ha hb
    | true =>
      simp only [d23058, d197065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23059 q = 1) (hb : d116753 q = 1) : d197066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23059, d197066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23059, d197066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150263 q = 1) : d197067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150263, d197067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150263, d197067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150264 q = 1) : d197068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150264, d197068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150264, d197068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150265 q = 1) : d197069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150265, d197069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150265, d197069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150266 q = 1) : d197070 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150266, d197070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150266, d197070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46742 (p : Pattern) (ha : d116753 p = 1) (hb : d150272 p = 1) : d197087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22737 q = 1) (hb : d116753 q = 1) : d196904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22737, d196904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22737, d196904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46696 q ha hb
  have h2 (q : Pattern) (ha : d22738 q = 1) (hb : d116753 q = 1) : d196905 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22738, d196905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22738, d196905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22747 q = 1) (hb : d116753 q = 1) : d196914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d196914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46696 q ha hb
    | true =>
      simp only [d22747, d196914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46699 q ha hb
  have h4 (q : Pattern) (ha : d22748 q = 1) (hb : d116753 q = 1) : d196915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d196915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22748, d196915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22749 q = 1) (hb : d116753 q = 1) : d196916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22749, d196916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22749, d196916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150250 q = 1) : d196988 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150250, d196988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46721 q ha hb
    | true =>
      simp only [d150250, d196988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46729 q ha hb
  have h7 (q : Pattern) (ha : d22916 q = 1) (hb : d116753 q = 1) : d197001 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22916, d197001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46703 q ha hb
    | true =>
      simp only [d22916, d197001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46704 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150251 q = 1) : d197002 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150251, d197002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150251, d197002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150252 q = 1) : d197003 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150252, d197003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150252, d197003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150253 q = 1) : d197004 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150253, d197004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150253, d197004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150257 q = 1) : d197008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150257, d197008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150257, d197008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46730 q ha hb
  have h12 (q : Pattern) (ha : d22925 q = 1) (hb : d116753 q = 1) : d197010 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22925, d197010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22925, d197010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46705 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150258 q = 1) : d197011 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150258, d197011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150258, d197011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150259 q = 1) : d197012 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150259, d197012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150259, d197012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150260 q = 1) : d197013 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150260, d197013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150260, d197013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150261 q = 1) : d197014 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150261, d197014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150261, d197014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116753 q = 1) (hb : d150267 q = 1) : d197071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150267, d197071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150267, d197071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46741 q ha hb
  have h18 (q : Pattern) (ha : d23075 q = 1) (hb : d116753 q = 1) : d197082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23075, d197082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23075, d197082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46710 q ha hb
  have h19 (q : Pattern) (ha : d116753 q = 1) (hb : d150268 q = 1) : d197083 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150268, d197083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150268, d197083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116753 q = 1) (hb : d150269 q = 1) : d197084 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150269, d197084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150269, d197084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116753 q = 1) (hb : d150270 q = 1) : d197085 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150270, d197085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150270, d197085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116753 q = 1) (hb : d150271 q = 1) : d197086 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150271, d197086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150271, d197086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150272 q = 1) : d197087 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150272, d197087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150272, d197087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46743 (p : Pattern) (ha : d116753 p = 1) (hb : d150278 p = 1) : d197093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150273 q = 1) : d197088 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150273, d197088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150273, d197088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46742 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150274 q = 1) : d197089 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150274, d197089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150274, d197089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150275 q = 1) : d197090 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150275, d197090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150275, d197090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150276 q = 1) : d197091 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150276, d197091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150276, d197091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150277 q = 1) : d197092 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150277, d197092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150277, d197092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150278 q = 1) : d197093 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150278, d197093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150278, d197093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46744 (p : Pattern) (ha : d116753 p = 1) (hb : d150284 p = 1) : d197099 p = 1 := by
  have h0 (q : Pattern) (ha : d116753 q = 1) (hb : d150113 q = 1) : d196264 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150113, d196264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46494 q ha hb
    | true =>
      simp only [d150113, d196264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46534 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150153 q = 1) : d196416 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150153, d196416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150153, d196416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46578 q ha hb
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150154 q = 1) : d196417 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150154, d196417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150154, d196417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150194 q = 1) : d196641 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150194, d196641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150194, d196641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46633 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150195 q = 1) : d196642 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150195, d196642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150195, d196642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150196 q = 1) : d196643 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150196, d196643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150196, d196643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150236 q = 1) : d196867 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150236, d196867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150236, d196867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46688 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150237 q = 1) : d196868 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150237, d196868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150237, d196868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150238 q = 1) : d196869 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150238, d196869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150238, d196869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150239 q = 1) : d196870 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150239, d196870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150239, d196870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150279 q = 1) : d197094 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150279, d197094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150279, d197094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46743 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150280 q = 1) : d197095 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150280, d197095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150280, d197095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150281 q = 1) : d197096 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150281, d197096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150281, d197096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150282 q = 1) : d197097 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150282, d197097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150282, d197097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150283 q = 1) : d197098 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150283, d197098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150283, d197098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150284 q = 1) : d197099 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150284, d197099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150284, d197099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro46745 (p : Pattern) (ha : d116753 p = 1) (hb : d150290 p = 1) : d197105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150285 q = 1) : d197100 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150285, d197100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46744 q ha hb
    | true =>
      simp only [d150285, d197100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150286 q = 1) : d197101 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150286, d197101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150286, d197101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150287 q = 1) : d197102 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150287, d197102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150287, d197102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150288 q = 1) : d197103 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150288, d197103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150288, d197103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150289 q = 1) : d197104 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150289, d197104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150289, d197104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150290 q = 1) : d197105 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150290, d197105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150290, d197105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46746 (p : Pattern) (ha : d116753 p = 1) (hb : d150296 p = 1) : d197111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150291 q = 1) : d197106 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150291, d197106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46745 q ha hb
    | true =>
      simp only [d150291, d197106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150292 q = 1) : d197107 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150292, d197107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150292, d197107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150293 q = 1) : d197108 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150293, d197108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150293, d197108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150294 q = 1) : d197109 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150294, d197109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150294, d197109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150295 q = 1) : d197110 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150295, d197110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150295, d197110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150296 q = 1) : d197111 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150296, d197111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150296, d197111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46747 (p : Pattern) (ha : d116753 p = 1) (hb : d150302 p = 1) : d197117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150297 q = 1) : d197112 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150297, d197112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46746 q ha hb
    | true =>
      simp only [d150297, d197112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150298 q = 1) : d197113 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150298, d197113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150298, d197113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150299 q = 1) : d197114 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150299, d197114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150299, d197114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150300 q = 1) : d197115 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150300, d197115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150300, d197115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150301 q = 1) : d197116 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150301, d197116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150301, d197116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150302 q = 1) : d197117 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d197117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150302, d197117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46748 (p : Pattern) (ha : d116753 p = 1) (hb : d150308 p = 1) : d197123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150303 q = 1) : d197118 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, d197118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46747 q ha hb
    | true =>
      simp only [d150303, d197118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150304 q = 1) : d197119 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, d197119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, d197119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150305 q = 1) : d197120 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, d197120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, d197120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150306 q = 1) : d197121 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, d197121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, d197121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150307 q = 1) : d197122 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, d197122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, d197122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150308 q = 1) : d197123 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, d197123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, d197123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46749 (p : Pattern) (ha : d116753 p = 1) (hb : d150314 p = 1) : d197129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116753 q = 1) (hb : d150309 q = 1) : d197124 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, d197124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46748 q ha hb
    | true =>
      simp only [d150309, d197124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150310 q = 1) : d197125 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, d197125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, d197125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d116753 q = 1) (hb : d150311 q = 1) : d197126 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, d197126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, d197126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d116753 q = 1) (hb : d150312 q = 1) : d197127 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, d197127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, d197127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150313 q = 1) : d197128 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, d197128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, d197128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150314 q = 1) : d197129 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, d197129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, d197129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
