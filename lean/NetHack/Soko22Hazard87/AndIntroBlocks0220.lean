import NetHack.Soko22Hazard87.AndIntroBlocks0219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro55000 (p : Pattern) (ha : d15972 p = 1) (hb : d169388 p = 1) : d14085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d169388 q = 1) : d14080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54999 q ha hb
    | true =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54981 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d169388 q = 1) : d14081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d169388 q = 1) : d14082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d169388 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d169388 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54981 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d169388 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d169388 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d169388 q = 1) : d14083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d169388 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d169388 q = 1) : d13985 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d169388 q = 1) : d14084 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d169388 q = 1) : d14085 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro55001 (p : Pattern) (ha : d15978 p = 1) (hb : d169388 p = 1) : d14091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d169388 q = 1) : d14086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55000 q ha hb
    | true =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d169388 q = 1) : d14087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d169388 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54982 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d169388 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d169388 q = 1) : d14088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d169388 q = 1) : d14089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d169388 q = 1) : d14090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d169388 q = 1) : d14091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55002 (p : Pattern) (ha : d128195 p = 1) (hb : d169388 p = 1) : d125455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d169388 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d169388 q = 1) : d14067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54996 q ha hb
    | true =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d169388 q = 1) : d14068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d169388 q = 1) : d14069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d169388 q = 1) : d14070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d169388 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d169388 q = 1) : d14074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54997 q ha hb
    | true =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d169388 q = 1) : d14075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d169388 q = 1) : d14076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d169388 q = 1) : d14092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55001 q ha hb
    | true =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54989 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d169388 q = 1) : d125451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d169388 q = 1) : d14113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54998 q ha hb
    | true =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d169388 q = 1) : d14114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d169388 q = 1) : d125452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d169388 q = 1) : d125453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d169388 q = 1) : d125454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d169388 q = 1) : d125455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro55003 (p : Pattern) (ha : d376 p = 1) (hb : d169388 p = 1) : d14119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d169388 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54982 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d169388 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169388 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d169388 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d169388 q = 1) : d13991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d169388 q = 1) : d14065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d169388 q = 1) : d14119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55004 (p : Pattern) (ha : d381 p = 1) (hb : d169388 p = 1) : d14124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d169388 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54982 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d169388 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169388 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d169388 q = 1) : d13990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d169388 q = 1) : d14071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d169388 q = 1) : d14072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d169388 q = 1) : d14124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55005 (p : Pattern) (ha : d5355 p = 1) (hb : d169388 p = 1) : d14133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d169388 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54982 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d169388 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d169388 q = 1) : d14109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d169388 q = 1) : d14110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d169388 q = 1) : d14111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d169388 q = 1) : d14133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55006 (p : Pattern) (ha : d15985 p = 1) (hb : d169388 p = 1) : d14128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d169388 q = 1) : d14086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55000 q ha hb
    | true =>
      simp only [d15973, d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d169388 q = 1) : d14087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d169388 q = 1) : d13988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54982 q ha hb
    | true =>
      simp only [d151, d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d169388 q = 1) : d13989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d169388 q = 1) : d14088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d169388 q = 1) : d14089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d169388 q = 1) : d14090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d169388 q = 1) : d14128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55007 (p : Pattern) (ha : d128200 p = 1) (hb : d169388 p = 1) : d125460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d169388 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d169388 q = 1) : d14067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54996 q ha hb
    | true =>
      simp only [d297, d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d169388 q = 1) : d14068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d169388 q = 1) : d14069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d169388 q = 1) : d14070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d169388 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d169388 q = 1) : d14074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54997 q ha hb
    | true =>
      simp only [d304, d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d169388 q = 1) : d14075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d169388 q = 1) : d14076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d169388 q = 1) : d14092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55001 q ha hb
    | true =>
      simp only [d15979, d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54989 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d169388 q = 1) : d125451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d169388 q = 1) : d14113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54998 q ha hb
    | true =>
      simp only [d4737, d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d169388 q = 1) : d14114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d169388 q = 1) : d125452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d169388 q = 1) : d125453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d169388 q = 1) : d125454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d169388 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d169388 q = 1) : d14120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55003 q ha hb
    | true =>
      simp only [d377, d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d169388 q = 1) : d14121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d169388 q = 1) : d14122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d169388 q = 1) : d14123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d169388 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d169388 q = 1) : d14125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55004 q ha hb
    | true =>
      simp only [d382, d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d169388 q = 1) : d14126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d169388 q = 1) : d14127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d169388 q = 1) : d14129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55006 q ha hb
    | true =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54983 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d169388 q = 1) : d125456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d169388 q = 1) : d14134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55005 q ha hb
    | true =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d169388 q = 1) : d14135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d169388 q = 1) : d125457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d169388 q = 1) : d125458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d169388 q = 1) : d125459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d169388 q = 1) : d125460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro55008 (p : Pattern) (ha : d128207 p = 1) (hb : d169388 p = 1) : d125467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d169388 q = 1) : d14129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55006 q ha hb
    | true =>
      simp only [d15986, d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54983 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d169388 q = 1) : d125456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d169388 q = 1) : d14134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55005 q ha hb
    | true =>
      simp only [d5356, d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d169388 q = 1) : d14135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d169388 q = 1) : d125457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d169388 q = 1) : d125465 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d169388 q = 1) : d125466 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d169388 q = 1) : d125467 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55009 (p : Pattern) (ha : d5377 p = 1) (hb : d169388 p = 1) : d14189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d169388 q = 1) : d14027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54986 q ha hb
    | true =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d169388 q = 1) : d14028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d169388 q = 1) : d14186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d169388 q = 1) : d14187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d169388 q = 1) : d14188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d169388 q = 1) : d14189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55010 (p : Pattern) (ha : d16004 p = 1) (hb : d169388 p = 1) : d14156 p = 1 := by
  have h0 (q : Pattern) (ha : d415 q = 1) (hb : d128484 q = 1) : d415 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d416 q = 1) (hb : d169388 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d169388, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d416, d169388, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12602 q = 1) (hb : d128484 q = 1) : d12602 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12603 q = 1) (hb : d169388 q = 1) : d14155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d169388, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12603, d169388, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16004 q = 1) (hb : d169388 q = 1) : d14156 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d14156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16004, d14156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55011 (p : Pattern) (ha : d16010 p = 1) (hb : d169388 p = 1) : d14162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d169388 q = 1) : d14157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55010 q ha hb
    | true =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54985 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d169388 q = 1) : d14158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d169388 q = 1) : d14159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d169388 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d169388 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54985 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d169388 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d169388 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d169388 q = 1) : d14160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d169388 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d169388 q = 1) : d14024 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d169388 q = 1) : d14161 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d169388 q = 1) : d14162 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro55012 (p : Pattern) (ha : d16016 p = 1) (hb : d169388 p = 1) : d14168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d169388 q = 1) : d14163 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55011 q ha hb
    | true =>
      simp only [d16011, d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d169388 q = 1) : d14164 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d169388 q = 1) : d14027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54986 q ha hb
    | true =>
      simp only [d238, d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d169388 q = 1) : d14028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d169388 q = 1) : d14165 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d169388 q = 1) : d14166 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d169388 q = 1) : d14167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d169388 q = 1) : d14168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55013 (p : Pattern) (ha : d128217 p = 1) (hb : d169388 p = 1) : d125477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d169388 q = 1) : d14169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55012 q ha hb
    | true =>
      simp only [d16017, d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54987 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d169388 q = 1) : d125473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d169388 q = 1) : d14190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55009 q ha hb
    | true =>
      simp only [d5378, d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d169388 q = 1) : d14191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d169388 q = 1) : d125474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d169388 q = 1) : d125475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d169388 q = 1) : d125476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d169388 q = 1) : d125477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55014 (p : Pattern) (ha : d128223 p = 1) (hb : d169388 p = 1) : d125483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d169388 q = 1) : d14055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54993 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d169388 q = 1) : d14056 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d169388 q = 1) : d14062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54993 q ha hb
    | true =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54994 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d169388 q = 1) : d14063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d169388 q = 1) : d14064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d169388 q = 1) : d125461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55002 q ha hb
    | true =>
      simp only [d128201, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55007 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d169388 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d169388 q = 1) : d14142 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54995 q ha hb
    | true =>
      simp only [d398, d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d169388 q = 1) : d125462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d169388 q = 1) : d125463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d169388 q = 1) : d125464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d169388 q = 1) : d125468 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55008 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d169388 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d169388 q = 1) : d125469 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d169388 q = 1) : d125470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d169388 q = 1) : d125471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d169388 q = 1) : d125472 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d169388 q = 1) : d125478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55013 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d169388 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d169388 q = 1) : d125479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d169388 q = 1) : d125480 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d169388 q = 1) : d125481 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d169388 q = 1) : d125482 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d169388 q = 1) : d125483 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro55015 (p : Pattern) (ha : d128229 p = 1) (hb : d169388 p = 1) : d125489 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d169388 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d169388 q = 1) : d125446 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54992 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d169388 q = 1) : d125447 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d169388 q = 1) : d125448 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d169388 q = 1) : d125449 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d169388 q = 1) : d125450 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d169388 q = 1) : d125484 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55014 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d169388 q = 1) : d125485 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d169388 q = 1) : d125486 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d169388 q = 1) : d125487 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d169388 q = 1) : d125488 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d169388 q = 1) : d125489 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro55016 (p : Pattern) (ha : d481 p = 1) (hb : d169388 p = 1) : d14214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d169388 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d169388 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54981 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d169388 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d169388 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d169388 q = 1) : d14208 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d169388 q = 1) : d14213 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d169388 q = 1) : d14214 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55017 (p : Pattern) (ha : d491 p = 1) (hb : d169388 p = 1) : d14224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d169388 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d169388 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d169388 q = 1) : d14223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d169388 q = 1) : d14224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55018 (p : Pattern) (ha : d501 p = 1) (hb : d169388 p = 1) : d14234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d169388 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d169388 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d169388 q = 1) : d14223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d169388 q = 1) : d14234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55019 (p : Pattern) (ha : d644 p = 1) (hb : d169388 p = 1) : d14355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d169388 q = 1) : d14344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55017 q ha hb
    | true =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d169388 q = 1) : d14345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d169388 q = 1) : d14346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d169388 q = 1) : d14347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d169388 q = 1) : d14348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d169388 q = 1) : d14350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55018 q ha hb
    | true =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d169388 q = 1) : d14351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d169388 q = 1) : d14352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d169388 q = 1) : d14353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d169388 q = 1) : d14354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d169388 q = 1) : d14355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55020 (p : Pattern) (ha : d653 p = 1) (hb : d169388 p = 1) : d14364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d169388 q = 1) : d14350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55018 q ha hb
    | true =>
      simp only [d639, d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d169388 q = 1) : d14351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d169388 q = 1) : d14352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d169388 q = 1) : d14353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d169388 q = 1) : d14354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d169388 q = 1) : d14364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55021 (p : Pattern) (ha : d683 p = 1) (hb : d169388 p = 1) : d14395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d169388 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d169388 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54985 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d169388 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d169388 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d169388 q = 1) : d14385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d169388 q = 1) : d14394 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d169388 q = 1) : d14395 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55022 (p : Pattern) (ha : d730 p = 1) (hb : d169388 p = 1) : d14447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d169388 q = 1) : d14396 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55021 q ha hb
    | true =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d169388 q = 1) : d14397 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d169388 q = 1) : d14444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d169388 q = 1) : d14445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d169388 q = 1) : d14446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d169388 q = 1) : d14447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55023 (p : Pattern) (ha : d736 p = 1) (hb : d169388 p = 1) : d14453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d169388 q = 1) : d14448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55022 q ha hb
    | true =>
      simp only [d731, d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d169388 q = 1) : d14449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d169388 q = 1) : d14450 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d169388 q = 1) : d14451 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d169388 q = 1) : d14452 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d169388 q = 1) : d14453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55024 (p : Pattern) (ha : d16036 p = 1) (hb : d169388 p = 1) : d14210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d169388 q = 1) : d14080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54999 q ha hb
    | true =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54981 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d169388 q = 1) : d14081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d169388 q = 1) : d14082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d169388 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d169388 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54981 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d169388 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d169388 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d169388 q = 1) : d14083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d169388 q = 1) : d14208 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d169388 q = 1) : d14209 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d169388 q = 1) : d14210 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55025 (p : Pattern) (ha : d16042 p = 1) (hb : d169388 p = 1) : d14220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d169388 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d169388 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d169388 q = 1) : d14219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d169388 q = 1) : d14220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55026 (p : Pattern) (ha : d16048 p = 1) (hb : d169388 p = 1) : d14230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d169388 q = 1) : d14225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55025 q ha hb
    | true =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55017 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d169388 q = 1) : d14226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d169388 q = 1) : d14227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d169388 q = 1) : d14228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d169388 q = 1) : d14229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d169388 q = 1) : d14230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55027 (p : Pattern) (ha : d16051 p = 1) (hb : d169388 p = 1) : d14233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d169388 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d169388 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d169388 q = 1) : d14219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d169388 q = 1) : d14233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55028 (p : Pattern) (ha : d16057 p = 1) (hb : d169388 p = 1) : d14240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d169388 q = 1) : d14225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55025 q ha hb
    | true =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55017 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d169388 q = 1) : d14226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d169388 q = 1) : d14227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d169388 q = 1) : d14228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d169388 q = 1) : d14229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d169388 q = 1) : d14235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55027 q ha hb
    | true =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55018 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d169388 q = 1) : d14236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d169388 q = 1) : d14237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d169388 q = 1) : d14238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d169388 q = 1) : d14239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d169388 q = 1) : d14240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55029 (p : Pattern) (ha : d16143 p = 1) (hb : d169388 p = 1) : d14349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d169388 q = 1) : d14225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55025 q ha hb
    | true =>
      simp only [d16043, d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55017 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d169388 q = 1) : d14226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d169388 q = 1) : d14227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d169388 q = 1) : d14228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d169388 q = 1) : d14229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d169388 q = 1) : d14344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55017 q ha hb
    | true =>
      simp only [d633, d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d169388 q = 1) : d14345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d169388 q = 1) : d14346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d169388 q = 1) : d14347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d169388 q = 1) : d14348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d169388 q = 1) : d14349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55030 (p : Pattern) (ha : d514 p = 1) (hb : d169388 p = 1) : d14247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d169388 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d169388 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d169388 q = 1) : d14246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d169388 q = 1) : d14247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55031 (p : Pattern) (ha : d524 p = 1) (hb : d169388 p = 1) : d14257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d169388 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d169388 q = 1) : d14255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d169388 q = 1) : d14256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d169388 q = 1) : d14257 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55032 (p : Pattern) (ha : d16062 p = 1) (hb : d169388 p = 1) : d14245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d169388 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d169388 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d169388 q = 1) : d14244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d169388 q = 1) : d14245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55033 (p : Pattern) (ha : d16069 p = 1) (hb : d169388 p = 1) : d14254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d169388 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d169388 q = 1) : d14252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d169388 q = 1) : d14253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d169388 q = 1) : d14254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55034 (p : Pattern) (ha : d16077 p = 1) (hb : d169388 p = 1) : d14263 p = 1 := by
  have h0 (q : Pattern) (ha : d546 q = 1) (hb : d128484 q = 1) : d546 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16074 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16075 q = 1) (hb : d169388 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d169388, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16075, d169388, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12749 q = 1) (hb : d128484 q = 1) : d12749 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12494 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16076 q = 1) (hb : d169388 q = 1) : d14262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d169388, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16076, d169388, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16077 q = 1) (hb : d169388 q = 1) : d14263 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16077, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55035 (p : Pattern) (ha : d16081 p = 1) (hb : d169388 p = 1) : d14267 p = 1 := by
  have h0 (q : Pattern) (ha : d12494 q = 1) (hb : d128484 q = 1) : d12494 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12495 q = 1) (hb : d169388 q = 1) : d14078 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d169388, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12495, d169388, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d29 q = 1) (hb : d169388 q = 1) : d29 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16081 q = 1) (hb : d169388 q = 1) : d14267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d14267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16081, d14267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55036 (p : Pattern) (ha : d16087 p = 1) (hb : d169388 p = 1) : d14273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d169388 q = 1) : d14264 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d14264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55034 q ha hb
    | true =>
      simp only [d16078, d14264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54999 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d169388 q = 1) : d14265 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d14265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d14265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d169388 q = 1) : d14266 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d14266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d14266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d169388 q = 1) : d14268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d14268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54999 q ha hb
    | true =>
      simp only [d16082, d14268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55035 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d169388 q = 1) : d14269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d14269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d14269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d169388 q = 1) : d14270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d14270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d14270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d169388 q = 1) : d14271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d169388 q = 1) : d14080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54999 q ha hb
    | true =>
      simp only [d15967, d14080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54981 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d169388 q = 1) : d14081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d14081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d169388 q = 1) : d14082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d14082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d169388 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d169388 q = 1) : d13982 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54981 q ha hb
    | true =>
      simp only [d145, d13982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d169388 q = 1) : d13983 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d13983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d169388 q = 1) : d13984 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d13984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d169388 q = 1) : d14083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16086 q = 1) (hb : d169388 q = 1) : d14272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16087 q = 1) (hb : d169388 q = 1) : d14273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16087, d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55037 (p : Pattern) (ha : d16093 p = 1) (hb : d169388 p = 1) : d14279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d169388 q = 1) : d14274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55036 q ha hb
    | true =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d169388 q = 1) : d14275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d169388 q = 1) : d14276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d169388 q = 1) : d14277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d169388 q = 1) : d14278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d169388 q = 1) : d14279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55038 (p : Pattern) (ha : d16114 p = 1) (hb : d169388 p = 1) : d14312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d169388 q = 1) : d14309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d169388 q = 1) : d14310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d169388 q = 1) : d14311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d169388 q = 1) : d14312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55039 (p : Pattern) (ha : d128234 p = 1) (hb : d169388 p = 1) : d125494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d169388 q = 1) : d14248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55032 q ha hb
    | true =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55030 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d169388 q = 1) : d14249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d169388 q = 1) : d14250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d169388 q = 1) : d14251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d169388 q = 1) : d14258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55033 q ha hb
    | true =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55031 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d169388 q = 1) : d14259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d169388 q = 1) : d14260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d169388 q = 1) : d14280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55037 q ha hb
    | true =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55025 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d169388 q = 1) : d125490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d169388 q = 1) : d14313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55038 q ha hb
    | true =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d169388 q = 1) : d14314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d169388 q = 1) : d125491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d169388 q = 1) : d125492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d169388 q = 1) : d125493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128234 q = 1) (hb : d169388 q = 1) : d125494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55040 (p : Pattern) (ha : d610 p = 1) (hb : d169388 p = 1) : d14320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d169388 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d169388 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d169388 q = 1) : d14246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d169388 q = 1) : d14320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55041 (p : Pattern) (ha : d616 p = 1) (hb : d169388 p = 1) : d14326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d169388 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d169388 q = 1) : d14255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d169388 q = 1) : d14256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d169388 q = 1) : d14326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55042 (p : Pattern) (ha : d16121 p = 1) (hb : d169388 p = 1) : d14319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d169388 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d169388 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d169388 q = 1) : d14244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d169388 q = 1) : d14319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55043 (p : Pattern) (ha : d16126 p = 1) (hb : d169388 p = 1) : d14325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d169388 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55016 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d169388 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d169388 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d169388 q = 1) : d14252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d169388 q = 1) : d14253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d169388 q = 1) : d14325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55044 (p : Pattern) (ha : d16130 p = 1) (hb : d169388 p = 1) : d14330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d169388 q = 1) : d14274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55036 q ha hb
    | true =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d169388 q = 1) : d14275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d169388 q = 1) : d14276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d169388 q = 1) : d14277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d169388 q = 1) : d14278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d169388 q = 1) : d14330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55045 (p : Pattern) (ha : d16135 p = 1) (hb : d169388 p = 1) : d14336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d169388 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55024 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d169388 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d169388 q = 1) : d14309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d169388 q = 1) : d14310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d169388 q = 1) : d14311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d169388 q = 1) : d14336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55046 (p : Pattern) (ha : d128239 p = 1) (hb : d169388 p = 1) : d125499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d169388 q = 1) : d14248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55032 q ha hb
    | true =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55030 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d169388 q = 1) : d14249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d169388 q = 1) : d14250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d169388 q = 1) : d14251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d169388 q = 1) : d14258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55033 q ha hb
    | true =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55031 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d169388 q = 1) : d14259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d169388 q = 1) : d14260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d169388 q = 1) : d14280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55037 q ha hb
    | true =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55025 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d169388 q = 1) : d125490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d169388 q = 1) : d14313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55038 q ha hb
    | true =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d169388 q = 1) : d14314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d169388 q = 1) : d125491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d169388 q = 1) : d125492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d169388 q = 1) : d125493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d169388 q = 1) : d14321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55042 q ha hb
    | true =>
      simp only [d16122, d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55040 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d169388 q = 1) : d14322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d169388 q = 1) : d14323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d169388 q = 1) : d14324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d169388 q = 1) : d14327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55043 q ha hb
    | true =>
      simp only [d16127, d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55041 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d169388 q = 1) : d14328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d169388 q = 1) : d14329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d169388 q = 1) : d14331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55044 q ha hb
    | true =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55027 q ha hb
  have h23 (q : Pattern) (ha : d128235 q = 1) (hb : d169388 q = 1) : d125495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d169388 q = 1) : d14337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55045 q ha hb
    | true =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d169388 q = 1) : d14338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128236 q = 1) (hb : d169388 q = 1) : d125496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128237 q = 1) (hb : d169388 q = 1) : d125497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128237, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128238 q = 1) (hb : d169388 q = 1) : d125498 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128238, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128239 q = 1) (hb : d169388 q = 1) : d125499 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro55047 (p : Pattern) (ha : d128246 p = 1) (hb : d169388 p = 1) : d125506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d169388 q = 1) : d14331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55044 q ha hb
    | true =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55027 q ha hb
  have h2 (q : Pattern) (ha : d128235 q = 1) (hb : d169388 q = 1) : d125495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d169388 q = 1) : d14337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55045 q ha hb
    | true =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d169388 q = 1) : d14338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d169388 q = 1) : d125496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d169388 q = 1) : d125504 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d169388 q = 1) : d125505 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d169388 q = 1) : d125506 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55048 (p : Pattern) (ha : d16162 p = 1) (hb : d169388 p = 1) : d14372 p = 1 := by
  have h0 (q : Pattern) (ha : d662 q = 1) (hb : d128484 q = 1) : d662 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16160 q = 1) (hb : d169388 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d169388, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16160, d169388, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12861 q = 1) (hb : d128484 q = 1) : d12861 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12602 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16161 q = 1) (hb : d169388 q = 1) : d14371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d169388, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16161, d169388, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16162 q = 1) (hb : d169388 q = 1) : d14372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16162, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55049 (p : Pattern) (ha : d16166 p = 1) (hb : d169388 p = 1) : d14376 p = 1 := by
  have h0 (q : Pattern) (ha : d12602 q = 1) (hb : d128484 q = 1) : d12602 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12603 q = 1) (hb : d169388 q = 1) : d14155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d169388, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12603, d169388, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70 q = 1) (hb : d169388 q = 1) : d70 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16166 q = 1) (hb : d169388 q = 1) : d14376 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d14376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16166, d14376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55050 (p : Pattern) (ha : d16172 p = 1) (hb : d169388 p = 1) : d14382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d169388 q = 1) : d14373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d14373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55048 q ha hb
    | true =>
      simp only [d16163, d14373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55010 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d169388 q = 1) : d14374 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d14374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d14374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d169388 q = 1) : d14375 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d14375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d14375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d169388 q = 1) : d14377 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d14377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55010 q ha hb
    | true =>
      simp only [d16167, d14377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55049 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d169388 q = 1) : d14378 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d14378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d14378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d169388 q = 1) : d14379 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d14379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d14379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d169388 q = 1) : d14380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d169388 q = 1) : d14157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55010 q ha hb
    | true =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54985 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d169388 q = 1) : d14158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d169388 q = 1) : d14159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d169388 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d169388 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54985 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d169388 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d169388 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d169388 q = 1) : d14160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d169388 q = 1) : d14381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16172 q = 1) (hb : d169388 q = 1) : d14382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16172, d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55051 (p : Pattern) (ha : d16176 p = 1) (hb : d169388 p = 1) : d14387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d169388 q = 1) : d14157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55010 q ha hb
    | true =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54985 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d169388 q = 1) : d14158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d169388 q = 1) : d14159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d169388 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d169388 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54985 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d169388 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d169388 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d169388 q = 1) : d14160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d169388 q = 1) : d14385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d169388 q = 1) : d14386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d169388 q = 1) : d14387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55052 (p : Pattern) (ha : d16182 p = 1) (hb : d169388 p = 1) : d14393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d169388 q = 1) : d14383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55050 q ha hb
    | true =>
      simp only [d16173, d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d169388 q = 1) : d14384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d169388 q = 1) : d14388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55051 q ha hb
    | true =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d169388 q = 1) : d14389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d169388 q = 1) : d14390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d169388 q = 1) : d14391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d169388 q = 1) : d14392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d169388 q = 1) : d14393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55053 (p : Pattern) (ha : d16186 p = 1) (hb : d169388 p = 1) : d14401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d169388 q = 1) : d14388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55051 q ha hb
    | true =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d169388 q = 1) : d14389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d169388 q = 1) : d14396 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55021 q ha hb
    | true =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d169388 q = 1) : d14397 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d169388 q = 1) : d14398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d169388 q = 1) : d14399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d169388 q = 1) : d14400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d169388 q = 1) : d14401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55054 (p : Pattern) (ha : d16207 p = 1) (hb : d169388 p = 1) : d14436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d169388 q = 1) : d14388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55051 q ha hb
    | true =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d169388 q = 1) : d14389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d169388 q = 1) : d14433 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d169388 q = 1) : d14434 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d169388 q = 1) : d14435 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d169388 q = 1) : d14436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55055 (p : Pattern) (ha : d128256 p = 1) (hb : d169388 p = 1) : d125516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d169388 q = 1) : d14402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55052 q ha hb
    | true =>
      simp only [d16187, d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55053 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d169388 q = 1) : d125512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d169388 q = 1) : d14437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55054 q ha hb
    | true =>
      simp only [d16208, d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d169388 q = 1) : d14438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d169388 q = 1) : d125513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d169388 q = 1) : d125514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d169388 q = 1) : d125515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d169388 q = 1) : d125516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55056 (p : Pattern) (ha : d128262 p = 1) (hb : d169388 p = 1) : d125522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d169388 q = 1) : d14231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55026 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d169388 q = 1) : d14232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d169388 q = 1) : d14241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55026 q ha hb
    | true =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55028 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d169388 q = 1) : d14242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d169388 q = 1) : d14243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128240 q = 1) (hb : d169388 q = 1) : d125500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55039 q ha hb
    | true =>
      simp only [d128240, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55046 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d169388 q = 1) : d14356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55029 q ha hb
    | true =>
      simp only [d16144, d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55019 q ha hb
  have h8 (q : Pattern) (ha : d128241 q = 1) (hb : d169388 q = 1) : d125501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128242 q = 1) (hb : d169388 q = 1) : d125502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128243 q = 1) (hb : d169388 q = 1) : d125503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128243, d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128247 q = 1) (hb : d169388 q = 1) : d125507 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128247, d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55047 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d169388 q = 1) : d14365 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55020 q ha hb
  have h13 (q : Pattern) (ha : d128248 q = 1) (hb : d169388 q = 1) : d125508 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128249 q = 1) (hb : d169388 q = 1) : d125509 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128250 q = 1) (hb : d169388 q = 1) : d125510 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128251 q = 1) (hb : d169388 q = 1) : d125511 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128257 q = 1) (hb : d169388 q = 1) : d125517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128257, d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55055 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d169388 q = 1) : d14454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55023 q ha hb
  have h19 (q : Pattern) (ha : d128258 q = 1) (hb : d169388 q = 1) : d125518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128259 q = 1) (hb : d169388 q = 1) : d125519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128260 q = 1) (hb : d169388 q = 1) : d125520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128261 q = 1) (hb : d169388 q = 1) : d125521 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128262 q = 1) (hb : d169388 q = 1) : d125522 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro55057 (p : Pattern) (ha : d128268 p = 1) (hb : d169388 p = 1) : d125528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d169388 q = 1) : d125523 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55056 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d169388 q = 1) : d125524 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d169388 q = 1) : d125525 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d169388 q = 1) : d125526 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d169388 q = 1) : d125527 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d169388 q = 1) : d125528 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55058 (p : Pattern) (ha : d758 p = 1) (hb : d169388 p = 1) : d14467 p = 1 := by
  have h0 (q : Pattern) (ha : d322 q = 1) (hb : d128484 q = 1) : d322 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d755 q = 1) (hb : d169388 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d169388, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d755, d169388, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d757 q = 1) (hb : d169388 q = 1) : d757 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d758 q = 1) (hb : d169388 q = 1) : d14467 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d14467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d758, d14467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55059 (p : Pattern) (ha : d773 p = 1) (hb : d169388 p = 1) : d14481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d169388 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d763 q = 1) (hb : d169388 q = 1) : d14471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55058 q ha hb
    | true =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d764 q = 1) (hb : d169388 q = 1) : d14472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d765 q = 1) (hb : d169388 q = 1) : d14473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d767 q = 1) (hb : d169388 q = 1) : d14475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d772 q = 1) (hb : d169388 q = 1) : d14480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d772, d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d773 q = 1) (hb : d169388 q = 1) : d14481 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d773, d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55060 (p : Pattern) (ha : d783 p = 1) (hb : d169388 p = 1) : d14491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d169388 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d169388 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d169388 q = 1) : d14490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d169388 q = 1) : d14491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55061 (p : Pattern) (ha : d793 p = 1) (hb : d169388 p = 1) : d14501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d169388 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d169388 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d169388 q = 1) : d14490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d169388 q = 1) : d14501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55062 (p : Pattern) (ha : d950 p = 1) (hb : d169388 p = 1) : d14628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d169388 q = 1) : d14617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55060 q ha hb
    | true =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d169388 q = 1) : d14618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d169388 q = 1) : d14619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d169388 q = 1) : d14620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d169388 q = 1) : d14621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d169388 q = 1) : d14623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55061 q ha hb
    | true =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d169388 q = 1) : d14624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d169388 q = 1) : d14625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d169388 q = 1) : d14626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d169388 q = 1) : d14627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d169388 q = 1) : d14628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55063 (p : Pattern) (ha : d959 p = 1) (hb : d169388 p = 1) : d14637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d169388 q = 1) : d14623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55061 q ha hb
    | true =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d169388 q = 1) : d14624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d169388 q = 1) : d14625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d169388 q = 1) : d14626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d169388 q = 1) : d14627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d169388 q = 1) : d14637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55064 (p : Pattern) (ha : d981 p = 1) (hb : d169388 p = 1) : d14658 p = 1 := by
  have h0 (q : Pattern) (ha : d415 q = 1) (hb : d128484 q = 1) : d415 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d975 q = 1) (hb : d169388 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d169388, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d975, d169388, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d980 q = 1) (hb : d169388 q = 1) : d980 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d981 q = 1) (hb : d169388 q = 1) : d14658 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d14658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d981, d14658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55065 (p : Pattern) (ha : d1005 p = 1) (hb : d169388 p = 1) : d14680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d169388 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d987 q = 1) (hb : d169388 q = 1) : d14662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55064 q ha hb
    | true =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d169388 q = 1) : d14663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d169388 q = 1) : d14664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d169388 q = 1) : d14670 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1004 q = 1) (hb : d169388 q = 1) : d14679 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1004, d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1005 q = 1) (hb : d169388 q = 1) : d14680 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1005, d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55066 (p : Pattern) (ha : d1063 p = 1) (hb : d169388 p = 1) : d14736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d169388 q = 1) : d14681 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55065 q ha hb
    | true =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d169388 q = 1) : d14682 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d169388 q = 1) : d14733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d169388 q = 1) : d14734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d169388 q = 1) : d14735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d169388 q = 1) : d14736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55067 (p : Pattern) (ha : d1069 p = 1) (hb : d169388 p = 1) : d14742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d169388 q = 1) : d14737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55066 q ha hb
    | true =>
      simp only [d1064, d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d169388 q = 1) : d14738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d169388 q = 1) : d14739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d169388 q = 1) : d14740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d169388 q = 1) : d14741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d169388 q = 1) : d14742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55068 (p : Pattern) (ha : d16227 p = 1) (hb : d169388 p = 1) : d14263 p = 1 := by
  have h0 (q : Pattern) (ha : d546 q = 1) (hb : d128484 q = 1) : d546 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16074 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16075 q = 1) (hb : d169388 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d169388, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16075, d169388, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12749 q = 1) (hb : d128484 q = 1) : d12749 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12750 q = 1) (hb : d169388 q = 1) : d14262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d169388, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12750, d169388, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16227 q = 1) (hb : d169388 q = 1) : d14263 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16227, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55069 (p : Pattern) (ha : d16233 p = 1) (hb : d169388 p = 1) : d14477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d169388 q = 1) : d14468 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55068 q ha hb
    | true =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55058 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d169388 q = 1) : d14469 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d169388 q = 1) : d14470 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d169388 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d763 q = 1) (hb : d169388 q = 1) : d14471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55058 q ha hb
    | true =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d764 q = 1) (hb : d169388 q = 1) : d14472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d765 q = 1) (hb : d169388 q = 1) : d14473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16231 q = 1) (hb : d169388 q = 1) : d14474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d767 q = 1) (hb : d169388 q = 1) : d14475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16232 q = 1) (hb : d169388 q = 1) : d14476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16232, d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16233 q = 1) (hb : d169388 q = 1) : d14477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16233, d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55070 (p : Pattern) (ha : d16239 p = 1) (hb : d169388 p = 1) : d14487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d169388 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d169388 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d169388 q = 1) : d14486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d169388 q = 1) : d14487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55071 (p : Pattern) (ha : d16245 p = 1) (hb : d169388 p = 1) : d14497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d169388 q = 1) : d14492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55070 q ha hb
    | true =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55060 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d169388 q = 1) : d14493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d169388 q = 1) : d14494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d169388 q = 1) : d14495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d169388 q = 1) : d14496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d169388 q = 1) : d14497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55072 (p : Pattern) (ha : d16248 p = 1) (hb : d169388 p = 1) : d14500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d169388 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d169388 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d169388 q = 1) : d14486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d169388 q = 1) : d14500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55073 (p : Pattern) (ha : d16254 p = 1) (hb : d169388 p = 1) : d14507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d169388 q = 1) : d14492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55070 q ha hb
    | true =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55060 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d169388 q = 1) : d14493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d169388 q = 1) : d14494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d169388 q = 1) : d14495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d169388 q = 1) : d14496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d169388 q = 1) : d14502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55072 q ha hb
    | true =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55061 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d169388 q = 1) : d14503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d169388 q = 1) : d14504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d169388 q = 1) : d14505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d169388 q = 1) : d14506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d169388 q = 1) : d14507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55074 (p : Pattern) (ha : d16343 p = 1) (hb : d169388 p = 1) : d14622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d169388 q = 1) : d14492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55070 q ha hb
    | true =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55060 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d169388 q = 1) : d14493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d169388 q = 1) : d14494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d169388 q = 1) : d14495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d169388 q = 1) : d14496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d169388 q = 1) : d14617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55060 q ha hb
    | true =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d169388 q = 1) : d14618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d169388 q = 1) : d14619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d169388 q = 1) : d14620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d169388 q = 1) : d14621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d169388 q = 1) : d14622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55075 (p : Pattern) (ha : d806 p = 1) (hb : d169388 p = 1) : d14514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d169388 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d169388 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d169388 q = 1) : d14513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d169388 q = 1) : d14514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55076 (p : Pattern) (ha : d816 p = 1) (hb : d169388 p = 1) : d14524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d169388 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d169388 q = 1) : d14522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d169388 q = 1) : d14523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d169388 q = 1) : d14524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55077 (p : Pattern) (ha : d16259 p = 1) (hb : d169388 p = 1) : d14512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d169388 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d169388 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d169388 q = 1) : d14511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d169388 q = 1) : d14512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55078 (p : Pattern) (ha : d16266 p = 1) (hb : d169388 p = 1) : d14521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d169388 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d169388 q = 1) : d14519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d169388 q = 1) : d14520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d169388 q = 1) : d14521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55079 (p : Pattern) (ha : d16274 p = 1) (hb : d169388 p = 1) : d14532 p = 1 := by
  have h0 (q : Pattern) (ha : d837 q = 1) (hb : d128484 q = 1) : d837 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16271 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16272 q = 1) (hb : d169388 q = 1) : d14528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d169388, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16272, d169388, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14530 q = 1) (hb : d128484 q = 1) : d14530 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12749 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16273 q = 1) (hb : d169388 q = 1) : d14531 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d169388, d14531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16273, d169388, d14531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16274 q = 1) (hb : d169388 q = 1) : d14532 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d14532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16274, d14532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55080 (p : Pattern) (ha : d16278 p = 1) (hb : d169388 p = 1) : d14536 p = 1 := by
  have h0 (q : Pattern) (ha : d12749 q = 1) (hb : d128484 q = 1) : d12749 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12750 q = 1) (hb : d169388 q = 1) : d14262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d169388, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12750, d169388, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d757 q = 1) (hb : d169388 q = 1) : d757 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16278 q = 1) (hb : d169388 q = 1) : d14536 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d14536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16278, d14536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55081 (p : Pattern) (ha : d16284 p = 1) (hb : d169388 p = 1) : d14542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d169388 q = 1) : d14533 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d14533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55079 q ha hb
    | true =>
      simp only [d16275, d14533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55068 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d169388 q = 1) : d14534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d14534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d14534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d169388 q = 1) : d14535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d14535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d14535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d169388 q = 1) : d14537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d14537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55068 q ha hb
    | true =>
      simp only [d16279, d14537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55080 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d169388 q = 1) : d14538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d14538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d14538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d169388 q = 1) : d14539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d14539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d14539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d169388 q = 1) : d14540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d169388 q = 1) : d14468 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55068 q ha hb
    | true =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55058 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d169388 q = 1) : d14469 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d169388 q = 1) : d14470 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d169388 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d763 q = 1) (hb : d169388 q = 1) : d14471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55058 q ha hb
    | true =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d764 q = 1) (hb : d169388 q = 1) : d14472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d765 q = 1) (hb : d169388 q = 1) : d14473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16231 q = 1) (hb : d169388 q = 1) : d14474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16283 q = 1) (hb : d169388 q = 1) : d14541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16284 q = 1) (hb : d169388 q = 1) : d14542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16284, d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55082 (p : Pattern) (ha : d16290 p = 1) (hb : d169388 p = 1) : d14548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d169388 q = 1) : d14543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55081 q ha hb
    | true =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d169388 q = 1) : d14544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d169388 q = 1) : d14545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d169388 q = 1) : d14546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d169388 q = 1) : d14547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d169388 q = 1) : d14548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55083 (p : Pattern) (ha : d16314 p = 1) (hb : d169388 p = 1) : d14585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d169388 q = 1) : d14582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d169388 q = 1) : d14583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d169388 q = 1) : d14584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d169388 q = 1) : d14585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55084 (p : Pattern) (ha : d128274 p = 1) (hb : d169388 p = 1) : d125534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d169388 q = 1) : d14515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55077 q ha hb
    | true =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55075 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d169388 q = 1) : d14516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d169388 q = 1) : d14517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d169388 q = 1) : d14518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d169388 q = 1) : d14525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55078 q ha hb
    | true =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55076 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d169388 q = 1) : d14526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d169388 q = 1) : d14527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d169388 q = 1) : d14549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55082 q ha hb
    | true =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55070 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d169388 q = 1) : d125530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d169388 q = 1) : d14586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55083 q ha hb
    | true =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d169388 q = 1) : d14587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d169388 q = 1) : d125531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d169388 q = 1) : d125532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d169388 q = 1) : d125533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128274 q = 1) (hb : d169388 q = 1) : d125534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55085 (p : Pattern) (ha : d916 p = 1) (hb : d169388 p = 1) : d14593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d169388 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d169388 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d169388 q = 1) : d14513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d169388 q = 1) : d14593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55086 (p : Pattern) (ha : d922 p = 1) (hb : d169388 p = 1) : d14599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d169388 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d169388 q = 1) : d14522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d169388 q = 1) : d14523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d169388 q = 1) : d14599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55087 (p : Pattern) (ha : d16321 p = 1) (hb : d169388 p = 1) : d14592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d169388 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d169388 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d169388 q = 1) : d14511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d169388 q = 1) : d14592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55088 (p : Pattern) (ha : d16326 p = 1) (hb : d169388 p = 1) : d14598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d169388 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55059 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d169388 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d169388 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d169388 q = 1) : d14519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d169388 q = 1) : d14520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d169388 q = 1) : d14598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55089 (p : Pattern) (ha : d16330 p = 1) (hb : d169388 p = 1) : d14603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d169388 q = 1) : d14543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55081 q ha hb
    | true =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d169388 q = 1) : d14544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d169388 q = 1) : d14545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d169388 q = 1) : d14546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d169388 q = 1) : d14547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d169388 q = 1) : d14603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55090 (p : Pattern) (ha : d16335 p = 1) (hb : d169388 p = 1) : d14609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d169388 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55069 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d169388 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d169388 q = 1) : d14582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d169388 q = 1) : d14583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d169388 q = 1) : d14584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d169388 q = 1) : d14609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55091 (p : Pattern) (ha : d128279 p = 1) (hb : d169388 p = 1) : d125539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d169388 q = 1) : d14515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55077 q ha hb
    | true =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55075 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d169388 q = 1) : d14516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d169388 q = 1) : d14517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d169388 q = 1) : d14518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d169388 q = 1) : d14525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55078 q ha hb
    | true =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55076 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d169388 q = 1) : d14526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d169388 q = 1) : d14527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d169388 q = 1) : d14549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55082 q ha hb
    | true =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55070 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d169388 q = 1) : d125530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d169388 q = 1) : d14586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55083 q ha hb
    | true =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d169388 q = 1) : d14587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d169388 q = 1) : d125531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d169388 q = 1) : d125532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d169388 q = 1) : d125533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d169388 q = 1) : d14594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55087 q ha hb
    | true =>
      simp only [d16322, d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55085 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d169388 q = 1) : d14595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d169388 q = 1) : d14596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d169388 q = 1) : d14597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d169388 q = 1) : d14600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55088 q ha hb
    | true =>
      simp only [d16327, d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55086 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d169388 q = 1) : d14601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d169388 q = 1) : d14602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d169388 q = 1) : d14604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55089 q ha hb
    | true =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55072 q ha hb
  have h23 (q : Pattern) (ha : d128275 q = 1) (hb : d169388 q = 1) : d125535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d169388 q = 1) : d14610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55090 q ha hb
    | true =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d169388 q = 1) : d14611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128276 q = 1) (hb : d169388 q = 1) : d125536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128277 q = 1) (hb : d169388 q = 1) : d125537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128277, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128278 q = 1) (hb : d169388 q = 1) : d125538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128278, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128279 q = 1) (hb : d169388 q = 1) : d125539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro55092 (p : Pattern) (ha : d128286 p = 1) (hb : d169388 p = 1) : d125546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d169388 q = 1) : d14604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55089 q ha hb
    | true =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55072 q ha hb
  have h2 (q : Pattern) (ha : d128275 q = 1) (hb : d169388 q = 1) : d125535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d169388 q = 1) : d14610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55090 q ha hb
    | true =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d169388 q = 1) : d14611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d169388 q = 1) : d125536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d169388 q = 1) : d125544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d169388 q = 1) : d125545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d169388 q = 1) : d125546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55093 (p : Pattern) (ha : d16362 p = 1) (hb : d169388 p = 1) : d14649 p = 1 := by
  have h0 (q : Pattern) (ha : d968 q = 1) (hb : d128484 q = 1) : d968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16360 q = 1) (hb : d169388 q = 1) : d14643 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d169388, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16360, d169388, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14647 q = 1) (hb : d128484 q = 1) : d14647 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12861 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16361 q = 1) (hb : d169388 q = 1) : d14648 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d169388, d14648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16361, d169388, d14648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16362 q = 1) (hb : d169388 q = 1) : d14649 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d14649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16362, d14649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55094 (p : Pattern) (ha : d16363 p = 1) (hb : d169388 p = 1) : d14372 p = 1 := by
  have h0 (q : Pattern) (ha : d662 q = 1) (hb : d128484 q = 1) : d662 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16160 q = 1) (hb : d169388 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d169388, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16160, d169388, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12861 q = 1) (hb : d128484 q = 1) : d12861 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12862 q = 1) (hb : d169388 q = 1) : d14371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d169388, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12862, d169388, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16363 q = 1) (hb : d169388 q = 1) : d14372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16363, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55095 (p : Pattern) (ha : d16367 p = 1) (hb : d169388 p = 1) : d14653 p = 1 := by
  have h0 (q : Pattern) (ha : d12861 q = 1) (hb : d128484 q = 1) : d12861 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12862 q = 1) (hb : d169388 q = 1) : d14371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d169388, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12862, d169388, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d980 q = 1) (hb : d169388 q = 1) : d980 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16367 q = 1) (hb : d169388 q = 1) : d14653 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d14653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16367, d14653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55096 (p : Pattern) (ha : d16377 p = 1) (hb : d169388 p = 1) : d14667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d169388 q = 1) : d14650 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d14650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55093 q ha hb
    | true =>
      simp only [d16364, d14650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55094 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d169388 q = 1) : d14651 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d14651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d14651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d169388 q = 1) : d14652 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d14652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d14652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d169388 q = 1) : d14654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d14654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55094 q ha hb
    | true =>
      simp only [d16368, d14654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55095 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d169388 q = 1) : d14655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d14655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d14655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d169388 q = 1) : d14656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d14656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d14656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d169388 q = 1) : d14657 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d169388 q = 1) : d14659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55094 q ha hb
    | true =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55064 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d169388 q = 1) : d14660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d169388 q = 1) : d14661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d169388 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d987 q = 1) (hb : d169388 q = 1) : d14662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55064 q ha hb
    | true =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d988 q = 1) (hb : d169388 q = 1) : d14663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d989 q = 1) (hb : d169388 q = 1) : d14664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16375 q = 1) (hb : d169388 q = 1) : d14665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16376 q = 1) (hb : d169388 q = 1) : d14666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16377 q = 1) (hb : d169388 q = 1) : d14667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16377, d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55097 (p : Pattern) (ha : d16381 p = 1) (hb : d169388 p = 1) : d14672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d169388 q = 1) : d14659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55094 q ha hb
    | true =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55064 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d169388 q = 1) : d14660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d169388 q = 1) : d14661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d169388 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d987 q = 1) (hb : d169388 q = 1) : d14662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55064 q ha hb
    | true =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d988 q = 1) (hb : d169388 q = 1) : d14663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d989 q = 1) (hb : d169388 q = 1) : d14664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16375 q = 1) (hb : d169388 q = 1) : d14665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d169388 q = 1) : d14670 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16380 q = 1) (hb : d169388 q = 1) : d14671 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16380, d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16381 q = 1) (hb : d169388 q = 1) : d14672 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16381, d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55098 (p : Pattern) (ha : d16387 p = 1) (hb : d169388 p = 1) : d14678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d169388 q = 1) : d14668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55096 q ha hb
    | true =>
      simp only [d16378, d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d169388 q = 1) : d14669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d169388 q = 1) : d14673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55097 q ha hb
    | true =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d169388 q = 1) : d14674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d169388 q = 1) : d14675 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d169388 q = 1) : d14676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d169388 q = 1) : d14677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d169388 q = 1) : d14678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55099 (p : Pattern) (ha : d16391 p = 1) (hb : d169388 p = 1) : d14686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d169388 q = 1) : d14673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55097 q ha hb
    | true =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d169388 q = 1) : d14674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d169388 q = 1) : d14681 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55065 q ha hb
    | true =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d169388 q = 1) : d14682 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d169388 q = 1) : d14683 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d169388 q = 1) : d14684 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d169388 q = 1) : d14685 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d169388 q = 1) : d14686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55100 (p : Pattern) (ha : d16417 p = 1) (hb : d169388 p = 1) : d14725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d169388 q = 1) : d14673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55097 q ha hb
    | true =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d169388 q = 1) : d14674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d169388 q = 1) : d14722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d169388 q = 1) : d14723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d169388 q = 1) : d14724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d169388 q = 1) : d14725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55101 (p : Pattern) (ha : d128296 p = 1) (hb : d169388 p = 1) : d125556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d169388 q = 1) : d14687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55098 q ha hb
    | true =>
      simp only [d16392, d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55099 q ha hb
  have h2 (q : Pattern) (ha : d128292 q = 1) (hb : d169388 q = 1) : d125552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128292, d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d169388 q = 1) : d14726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55100 q ha hb
    | true =>
      simp only [d16418, d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d169388 q = 1) : d14727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d169388 q = 1) : d125553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d169388 q = 1) : d125554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d169388 q = 1) : d125555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d169388 q = 1) : d125556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55102 (p : Pattern) (ha : d128302 p = 1) (hb : d169388 p = 1) : d125562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16246 q = 1) (hb : d169388 q = 1) : d14498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16246, d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16246, d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55071 q ha hb
  have h2 (q : Pattern) (ha : d16247 q = 1) (hb : d169388 q = 1) : d14499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16247, d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16247, d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16255 q = 1) (hb : d169388 q = 1) : d14508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55071 q ha hb
    | true =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55073 q ha hb
  have h4 (q : Pattern) (ha : d16256 q = 1) (hb : d169388 q = 1) : d14509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16257 q = 1) (hb : d169388 q = 1) : d14510 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16257, d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16257, d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128280 q = 1) (hb : d169388 q = 1) : d125540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55084 q ha hb
    | true =>
      simp only [d128280, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55091 q ha hb
  have h7 (q : Pattern) (ha : d16344 q = 1) (hb : d169388 q = 1) : d14629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16344, d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55074 q ha hb
    | true =>
      simp only [d16344, d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55062 q ha hb
  have h8 (q : Pattern) (ha : d128281 q = 1) (hb : d169388 q = 1) : d125541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128281, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128282 q = 1) (hb : d169388 q = 1) : d125542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128282, d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128283 q = 1) (hb : d169388 q = 1) : d125543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128283, d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128287 q = 1) (hb : d169388 q = 1) : d125547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128287, d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55092 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d169388 q = 1) : d14638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55063 q ha hb
  have h13 (q : Pattern) (ha : d128288 q = 1) (hb : d169388 q = 1) : d125548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128288, d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128289 q = 1) (hb : d169388 q = 1) : d125549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128289, d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128290 q = 1) (hb : d169388 q = 1) : d125550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128290, d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128291 q = 1) (hb : d169388 q = 1) : d125551 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128291, d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128297 q = 1) (hb : d169388 q = 1) : d125557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128297, d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55101 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d169388 q = 1) : d14743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55067 q ha hb
  have h19 (q : Pattern) (ha : d128298 q = 1) (hb : d169388 q = 1) : d125558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128298, d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128299 q = 1) (hb : d169388 q = 1) : d125559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128299, d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128300 q = 1) (hb : d169388 q = 1) : d125560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128300, d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128301 q = 1) (hb : d169388 q = 1) : d125561 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128301, d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128302 q = 1) (hb : d169388 q = 1) : d125562 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128302, d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro55103 (p : Pattern) (ha : d128308 p = 1) (hb : d169388 p = 1) : d125568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d169388 q = 1) : d125563 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55102 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d169388 q = 1) : d125564 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d169388 q = 1) : d125565 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d169388 q = 1) : d125566 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d169388 q = 1) : d125567 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d169388 q = 1) : d125568 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55104 (p : Pattern) (ha : d16442 p = 1) (hb : d169388 p = 1) : d14761 p = 1 := by
  have h0 (q : Pattern) (ha : d1103 q = 1) (hb : d128484 q = 1) : d1103 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16439 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16440 q = 1) (hb : d169388 q = 1) : d14757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d169388, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16440, d169388, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14759 q = 1) (hb : d128484 q = 1) : d14759 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14764 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16441 q = 1) (hb : d169388 q = 1) : d14760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, d169388, d14760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16441, d169388, d14760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16442 q = 1) (hb : d169388 q = 1) : d14761 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d14761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16442, d14761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55105 (p : Pattern) (ha : d16443 p = 1) (hb : d169388 p = 1) : d14766 p = 1 := by
  have h0 (q : Pattern) (ha : d1113 q = 1) (hb : d128484 q = 1) : d1113 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1125 q = 1) (hb : d169388 q = 1) : d14762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d169388, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1125, d169388, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14765 q = 1) (hb : d169388 q = 1) : d14765 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16443 q = 1) (hb : d169388 q = 1) : d14766 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d14766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16443, d14766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55106 (p : Pattern) (ha : d16456 p = 1) (hb : d169388 p = 1) : d14784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d169388 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55104 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d169388 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d169388 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14773 q = 1) (hb : d169388 q = 1) : d14773 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d169388 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16448 q = 1) (hb : d169388 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16449 q = 1) (hb : d169388 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16450 q = 1) (hb : d169388 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14778 q = 1) (hb : d169388 q = 1) : d14778 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16451 q = 1) (hb : d169388 q = 1) : d14779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
    | true =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16452 q = 1) (hb : d169388 q = 1) : d14780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16453 q = 1) (hb : d169388 q = 1) : d14781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16454 q = 1) (hb : d169388 q = 1) : d14782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16455 q = 1) (hb : d169388 q = 1) : d14783 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16455, d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16456 q = 1) (hb : d169388 q = 1) : d14784 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16456, d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55107 (p : Pattern) (ha : d16460 p = 1) (hb : d169388 p = 1) : d14788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14778 q = 1) (hb : d169388 q = 1) : d14778 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16451 q = 1) (hb : d169388 q = 1) : d14779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
    | true =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16452 q = 1) (hb : d169388 q = 1) : d14780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16453 q = 1) (hb : d169388 q = 1) : d14781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16454 q = 1) (hb : d169388 q = 1) : d14782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16459 q = 1) (hb : d169388 q = 1) : d14787 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16459, d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16460 q = 1) (hb : d169388 q = 1) : d14788 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16460, d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55108 (p : Pattern) (ha : d16466 p = 1) (hb : d169388 p = 1) : d14794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d169388 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55106 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d169388 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d169388 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d169388 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d169388 q = 1) : d14793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16466 q = 1) (hb : d169388 q = 1) : d14794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16466, d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16466, d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55109 (p : Pattern) (ha : d16470 p = 1) (hb : d169388 p = 1) : d14798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d169388 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d169388 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d169388 q = 1) : d14797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16470 q = 1) (hb : d169388 q = 1) : d14798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16470, d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16470, d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55110 (p : Pattern) (ha : d16476 p = 1) (hb : d169388 p = 1) : d14804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d169388 q = 1) : d14799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55108 q ha hb
    | true =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55109 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d169388 q = 1) : d14800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d169388 q = 1) : d14801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d169388 q = 1) : d14802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d169388 q = 1) : d14803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16476 q = 1) (hb : d169388 q = 1) : d14804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16476, d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16476, d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55111 (p : Pattern) (ha : d16479 p = 1) (hb : d169388 p = 1) : d14807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d169388 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55106 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d169388 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d169388 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d169388 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d169388 q = 1) : d14793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16479 q = 1) (hb : d169388 q = 1) : d14807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16479, d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16479, d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55112 (p : Pattern) (ha : d16480 p = 1) (hb : d169388 p = 1) : d14808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d169388 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d169388 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d169388 q = 1) : d14797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16480 q = 1) (hb : d169388 q = 1) : d14808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16480, d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16480, d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55113 (p : Pattern) (ha : d16486 p = 1) (hb : d169388 p = 1) : d14814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d169388 q = 1) : d14799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55108 q ha hb
    | true =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55109 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d169388 q = 1) : d14800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d169388 q = 1) : d14801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d169388 q = 1) : d14802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d169388 q = 1) : d14803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16481 q = 1) (hb : d169388 q = 1) : d14809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55111 q ha hb
    | true =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55112 q ha hb
  have h7 (q : Pattern) (ha : d16482 q = 1) (hb : d169388 q = 1) : d14810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16483 q = 1) (hb : d169388 q = 1) : d14811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16484 q = 1) (hb : d169388 q = 1) : d14812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16485 q = 1) (hb : d169388 q = 1) : d14813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16486 q = 1) (hb : d169388 q = 1) : d14814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16486, d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16486, d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55114 (p : Pattern) (ha : d16527 p = 1) (hb : d169388 p = 1) : d14855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d169388 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55104 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d169388 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d169388 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14773 q = 1) (hb : d169388 q = 1) : d14773 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d169388 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16448 q = 1) (hb : d169388 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16449 q = 1) (hb : d169388 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16450 q = 1) (hb : d169388 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16525 q = 1) (hb : d169388 q = 1) : d14853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16525, d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16526 q = 1) (hb : d169388 q = 1) : d14854 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16526, d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16527 q = 1) (hb : d169388 q = 1) : d14855 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16527, d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16527, d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55115 (p : Pattern) (ha : d16537 p = 1) (hb : d169388 p = 1) : d14865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d169388 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55114 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d169388 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d169388 q = 1) : d14862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d169388 q = 1) : d14863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d169388 q = 1) : d14864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16537 q = 1) (hb : d169388 q = 1) : d14865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16537, d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16537, d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55116 (p : Pattern) (ha : d16628 p = 1) (hb : d169388 p = 1) : d14965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16618 q = 1) (hb : d169388 q = 1) : d14955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16618, d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55115 q ha hb
    | true =>
      simp only [d16618, d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55109 q ha hb
  have h2 (q : Pattern) (ha : d16619 q = 1) (hb : d169388 q = 1) : d14956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16619, d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16619, d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16620 q = 1) (hb : d169388 q = 1) : d14957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16620, d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16620, d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16621 q = 1) (hb : d169388 q = 1) : d14958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16621, d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16621, d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16622 q = 1) (hb : d169388 q = 1) : d14959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16622, d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16622, d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16623 q = 1) (hb : d169388 q = 1) : d14960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55109 q ha hb
    | true =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16624 q = 1) (hb : d169388 q = 1) : d14961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16625 q = 1) (hb : d169388 q = 1) : d14962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16626 q = 1) (hb : d169388 q = 1) : d14963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16627 q = 1) (hb : d169388 q = 1) : d14964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16628 q = 1) (hb : d169388 q = 1) : d14965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16628, d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16628, d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55117 (p : Pattern) (ha : d16634 p = 1) (hb : d169388 p = 1) : d14971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16623 q = 1) (hb : d169388 q = 1) : d14960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55109 q ha hb
    | true =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16624 q = 1) (hb : d169388 q = 1) : d14961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16625 q = 1) (hb : d169388 q = 1) : d14962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16626 q = 1) (hb : d169388 q = 1) : d14963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16627 q = 1) (hb : d169388 q = 1) : d14964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16629 q = 1) (hb : d169388 q = 1) : d14966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55112 q ha hb
    | true =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16630 q = 1) (hb : d169388 q = 1) : d14967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16631 q = 1) (hb : d169388 q = 1) : d14968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16632 q = 1) (hb : d169388 q = 1) : d14969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16633 q = 1) (hb : d169388 q = 1) : d14970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16634 q = 1) (hb : d169388 q = 1) : d14971 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16634, d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16634, d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55118 (p : Pattern) (ha : d16643 p = 1) (hb : d169388 p = 1) : d14980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16629 q = 1) (hb : d169388 q = 1) : d14966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55112 q ha hb
    | true =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16630 q = 1) (hb : d169388 q = 1) : d14967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16631 q = 1) (hb : d169388 q = 1) : d14968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16632 q = 1) (hb : d169388 q = 1) : d14969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16633 q = 1) (hb : d169388 q = 1) : d14970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16643 q = 1) (hb : d169388 q = 1) : d14980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16643, d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16643, d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55119 (p : Pattern) (ha : d16672 p = 1) (hb : d169388 p = 1) : d15015 p = 1 := by
  have h0 (q : Pattern) (ha : d1388 q = 1) (hb : d128484 q = 1) : d1388 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1395 q = 1) (hb : d169388 q = 1) : d15014 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d169388, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1395, d169388, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15008 q = 1) (hb : d169388 q = 1) : d15008 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16672 q = 1) (hb : d169388 q = 1) : d15015 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d15015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16672, d15015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55120 (p : Pattern) (ha : d16698 p = 1) (hb : d169388 p = 1) : d15048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15042 q = 1) (hb : d169388 q = 1) : d15042 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16693 q = 1) (hb : d169388 q = 1) : d15043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
    | true =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16694 q = 1) (hb : d169388 q = 1) : d15044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16695 q = 1) (hb : d169388 q = 1) : d15045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16696 q = 1) (hb : d169388 q = 1) : d15046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16697 q = 1) (hb : d169388 q = 1) : d15047 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16697, d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16698 q = 1) (hb : d169388 q = 1) : d15048 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16698, d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16698, d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55121 (p : Pattern) (ha : d16765 p = 1) (hb : d169388 p = 1) : d15128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16699 q = 1) (hb : d169388 q = 1) : d15049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55120 q ha hb
    | true =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16700 q = 1) (hb : d169388 q = 1) : d15050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16762 q = 1) (hb : d169388 q = 1) : d15125 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16762, d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16762, d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16763 q = 1) (hb : d169388 q = 1) : d15126 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16763, d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16763, d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16764 q = 1) (hb : d169388 q = 1) : d15127 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16764, d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16764, d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16765 q = 1) (hb : d169388 q = 1) : d15128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16765, d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16765, d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55122 (p : Pattern) (ha : d16771 p = 1) (hb : d169388 p = 1) : d15134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16766 q = 1) (hb : d169388 q = 1) : d15129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16766, d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55121 q ha hb
    | true =>
      simp only [d16766, d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16767 q = 1) (hb : d169388 q = 1) : d15130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16767, d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16767, d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16768 q = 1) (hb : d169388 q = 1) : d15131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16768, d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16768, d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16769 q = 1) (hb : d169388 q = 1) : d15132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16769, d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16769, d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16770 q = 1) (hb : d169388 q = 1) : d15133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16770, d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16770, d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16771 q = 1) (hb : d169388 q = 1) : d15134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16771, d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16771, d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55123 (p : Pattern) (ha : d16491 p = 1) (hb : d169388 p = 1) : d14819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d169388 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55106 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d169388 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d169388 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d169388 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d169388 q = 1) : d14818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16491 q = 1) (hb : d169388 q = 1) : d14819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16491, d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16491, d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55124 (p : Pattern) (ha : d16493 p = 1) (hb : d169388 p = 1) : d14821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d169388 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d169388 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d169388 q = 1) : d14820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16493 q = 1) (hb : d169388 q = 1) : d14821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16493, d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16493, d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55125 (p : Pattern) (ha : d16500 p = 1) (hb : d169388 p = 1) : d14828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d169388 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55106 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d169388 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d169388 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d169388 q = 1) : d14826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d169388 q = 1) : d14827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16500 q = 1) (hb : d169388 q = 1) : d14828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16500, d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16500, d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55126 (p : Pattern) (ha : d16503 p = 1) (hb : d169388 p = 1) : d14831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d169388 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d169388 q = 1) : d14829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d169388 q = 1) : d14830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16503 q = 1) (hb : d169388 q = 1) : d14831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16503, d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16503, d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55127 (p : Pattern) (ha : d16511 p = 1) (hb : d169388 p = 1) : d14839 p = 1 := by
  have h0 (q : Pattern) (ha : d1213 q = 1) (hb : d128484 q = 1) : d1213 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16508 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16509 q = 1) (hb : d169388 q = 1) : d14835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d169388, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16509, d169388, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14837 q = 1) (hb : d128484 q = 1) : d14837 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14759 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16510 q = 1) (hb : d169388 q = 1) : d14838 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16510, d169388, d14838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16510, d169388, d14838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16511 q = 1) (hb : d169388 q = 1) : d14839 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d14839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16511, d14839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55128 (p : Pattern) (ha : d16516 p = 1) (hb : d169388 p = 1) : d14844 p = 1 := by
  have h0 (q : Pattern) (ha : d13023 q = 1) (hb : d128484 q = 1) : d13023 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16515 q = 1) (hb : d169388 q = 1) : d14843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d169388, d14843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16515, d169388, d14843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14765 q = 1) (hb : d169388 q = 1) : d14765 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16516 q = 1) (hb : d169388 q = 1) : d14844 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d14844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16516, d14844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55129 (p : Pattern) (ha : d16522 p = 1) (hb : d169388 p = 1) : d14850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d169388 q = 1) : d14840 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d14840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55127 q ha hb
    | true =>
      simp only [d16512, d14840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55104 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d169388 q = 1) : d14841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d14841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d14841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d169388 q = 1) : d14842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d14842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d14842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d169388 q = 1) : d14845 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d14845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55104 q ha hb
    | true =>
      simp only [d16517, d14845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55128 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d169388 q = 1) : d14846 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d14846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d14846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d169388 q = 1) : d14847 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d14847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d14847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d169388 q = 1) : d14848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d169388 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55104 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d169388 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d169388 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14773 q = 1) (hb : d169388 q = 1) : d14773 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16447 q = 1) (hb : d169388 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16448 q = 1) (hb : d169388 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16449 q = 1) (hb : d169388 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16450 q = 1) (hb : d169388 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16521 q = 1) (hb : d169388 q = 1) : d14849 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16522 q = 1) (hb : d169388 q = 1) : d14850 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16522, d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16522, d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55130 (p : Pattern) (ha : d16533 p = 1) (hb : d169388 p = 1) : d14861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d169388 q = 1) : d14851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55129 q ha hb
    | true =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d169388 q = 1) : d14852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d169388 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55114 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d169388 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d169388 q = 1) : d14858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d169388 q = 1) : d14859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d169388 q = 1) : d14860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16533 q = 1) (hb : d169388 q = 1) : d14861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16533, d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16533, d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55131 (p : Pattern) (ha : d16579 p = 1) (hb : d169388 p = 1) : d14916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d169388 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55104 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d169388 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d169388 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14773 q = 1) (hb : d169388 q = 1) : d14773 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d169388 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16448 q = 1) (hb : d169388 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16449 q = 1) (hb : d169388 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16450 q = 1) (hb : d169388 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12961 q = 1) (hb : d169388 q = 1) : d12961 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16574 q = 1) (hb : d169388 q = 1) : d14911 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d14911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55105 q ha hb
    | true =>
      simp only [d16574, d14911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16575 q = 1) (hb : d169388 q = 1) : d14912 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d14912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d14912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16576 q = 1) (hb : d169388 q = 1) : d14913 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d14913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d14913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16577 q = 1) (hb : d169388 q = 1) : d14914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16577, d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16578 q = 1) (hb : d169388 q = 1) : d14915 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16578, d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16579 q = 1) (hb : d169388 q = 1) : d14916 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16579, d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16579, d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55132 (p : Pattern) (ha : d16585 p = 1) (hb : d169388 p = 1) : d14922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d169388 q = 1) : d14917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55131 q ha hb
    | true =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d169388 q = 1) : d14918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d169388 q = 1) : d14919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d169388 q = 1) : d14920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d169388 q = 1) : d14921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16585 q = 1) (hb : d169388 q = 1) : d14922 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16585, d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16585, d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55133 (p : Pattern) (ha : d128315 p = 1) (hb : d169388 p = 1) : d125575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d169388 q = 1) : d14822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55123 q ha hb
    | true =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55124 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d169388 q = 1) : d14823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d169388 q = 1) : d14824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d169388 q = 1) : d14825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d169388 q = 1) : d14832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55125 q ha hb
    | true =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55126 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d169388 q = 1) : d14833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d169388 q = 1) : d14834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d169388 q = 1) : d14866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55130 q ha hb
    | true =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55115 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d169388 q = 1) : d125571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d169388 q = 1) : d14923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55132 q ha hb
    | true =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d169388 q = 1) : d14924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d169388 q = 1) : d125572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d169388 q = 1) : d125573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d169388 q = 1) : d125574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128315 q = 1) (hb : d169388 q = 1) : d125575 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128315, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128315, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55134 (p : Pattern) (ha : d16592 p = 1) (hb : d169388 p = 1) : d14929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d169388 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55106 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d169388 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d169388 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d169388 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d169388 q = 1) : d14818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16592 q = 1) (hb : d169388 q = 1) : d14929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16592, d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16592, d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55135 (p : Pattern) (ha : d16593 p = 1) (hb : d169388 p = 1) : d14930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d169388 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d169388 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d169388 q = 1) : d14820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16593 q = 1) (hb : d169388 q = 1) : d14930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16593, d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16593, d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55136 (p : Pattern) (ha : d16598 p = 1) (hb : d169388 p = 1) : d14935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d169388 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55106 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d169388 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d169388 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d169388 q = 1) : d14826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d169388 q = 1) : d14827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16598 q = 1) (hb : d169388 q = 1) : d14935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16598, d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16598, d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55137 (p : Pattern) (ha : d16599 p = 1) (hb : d169388 p = 1) : d14936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d169388 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d169388 q = 1) : d14829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d169388 q = 1) : d14830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16599 q = 1) (hb : d169388 q = 1) : d14936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16599, d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16599, d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55138 (p : Pattern) (ha : d16603 p = 1) (hb : d169388 p = 1) : d14940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d169388 q = 1) : d14851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55129 q ha hb
    | true =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d169388 q = 1) : d14852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d169388 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55114 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d169388 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d169388 q = 1) : d14858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d169388 q = 1) : d14859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d169388 q = 1) : d14860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16603 q = 1) (hb : d169388 q = 1) : d14940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16603, d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16603, d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55139 (p : Pattern) (ha : d16604 p = 1) (hb : d169388 p = 1) : d14941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d169388 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55114 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d169388 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d169388 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55107 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d169388 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d169388 q = 1) : d14862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d169388 q = 1) : d14863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d169388 q = 1) : d14864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16604 q = 1) (hb : d169388 q = 1) : d14941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16604, d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16604, d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55140 (p : Pattern) (ha : d16610 p = 1) (hb : d169388 p = 1) : d14947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d169388 q = 1) : d14917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55131 q ha hb
    | true =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d169388 q = 1) : d14918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d169388 q = 1) : d14919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d169388 q = 1) : d14920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d169388 q = 1) : d14921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16610 q = 1) (hb : d169388 q = 1) : d14947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16610, d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16610, d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55141 (p : Pattern) (ha : d128320 p = 1) (hb : d169388 p = 1) : d125580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d169388 q = 1) : d14822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55123 q ha hb
    | true =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55124 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d169388 q = 1) : d14823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d169388 q = 1) : d14824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d169388 q = 1) : d14825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d169388 q = 1) : d14832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55125 q ha hb
    | true =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55126 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d169388 q = 1) : d14833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d169388 q = 1) : d14834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d169388 q = 1) : d14866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55130 q ha hb
    | true =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55115 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d169388 q = 1) : d125571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d169388 q = 1) : d14923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55132 q ha hb
    | true =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d169388 q = 1) : d14924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d169388 q = 1) : d125572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d169388 q = 1) : d125573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d169388 q = 1) : d125574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16594 q = 1) (hb : d169388 q = 1) : d14931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16594, d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55134 q ha hb
    | true =>
      simp only [d16594, d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55135 q ha hb
  have h16 (q : Pattern) (ha : d16595 q = 1) (hb : d169388 q = 1) : d14932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16595, d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16595, d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16596 q = 1) (hb : d169388 q = 1) : d14933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16596, d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16596, d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16597 q = 1) (hb : d169388 q = 1) : d14934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16597, d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16597, d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16600 q = 1) (hb : d169388 q = 1) : d14937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16600, d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55136 q ha hb
    | true =>
      simp only [d16600, d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55137 q ha hb
  have h20 (q : Pattern) (ha : d16601 q = 1) (hb : d169388 q = 1) : d14938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16601, d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16601, d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16602 q = 1) (hb : d169388 q = 1) : d14939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16602, d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16602, d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16605 q = 1) (hb : d169388 q = 1) : d14942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55138 q ha hb
    | true =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55139 q ha hb
  have h23 (q : Pattern) (ha : d128316 q = 1) (hb : d169388 q = 1) : d125576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16611 q = 1) (hb : d169388 q = 1) : d14948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55140 q ha hb
    | true =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16612 q = 1) (hb : d169388 q = 1) : d14949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128317 q = 1) (hb : d169388 q = 1) : d125577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128318 q = 1) (hb : d169388 q = 1) : d125578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128318, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128318, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128319 q = 1) (hb : d169388 q = 1) : d125579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128319, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128319, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128320 q = 1) (hb : d169388 q = 1) : d125580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128320, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128320, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro55142 (p : Pattern) (ha : d128327 p = 1) (hb : d169388 p = 1) : d125587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16605 q = 1) (hb : d169388 q = 1) : d14942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55138 q ha hb
    | true =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55139 q ha hb
  have h2 (q : Pattern) (ha : d128316 q = 1) (hb : d169388 q = 1) : d125576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16611 q = 1) (hb : d169388 q = 1) : d14948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55140 q ha hb
    | true =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16612 q = 1) (hb : d169388 q = 1) : d14949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128317 q = 1) (hb : d169388 q = 1) : d125577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128325 q = 1) (hb : d169388 q = 1) : d125585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128325, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128326 q = 1) (hb : d169388 q = 1) : d125586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128326, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d169388 q = 1) : d125587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55143 (p : Pattern) (ha : d16655 p = 1) (hb : d169388 p = 1) : d14992 p = 1 := by
  have h0 (q : Pattern) (ha : d1379 q = 1) (hb : d128484 q = 1) : d1379 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16653 q = 1) (hb : d169388 q = 1) : d14986 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d169388, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16653, d169388, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14990 q = 1) (hb : d128484 q = 1) : d14990 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14997 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16654 q = 1) (hb : d169388 q = 1) : d14991 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16654, d169388, d14991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16654, d169388, d14991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16655 q = 1) (hb : d169388 q = 1) : d14992 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d14992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16655, d14992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55144 (p : Pattern) (ha : d16662 p = 1) (hb : d169388 p = 1) : d14999 p = 1 := by
  have h0 (q : Pattern) (ha : d1383 q = 1) (hb : d128484 q = 1) : d1383 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16660 q = 1) (hb : d169388 q = 1) : d14993 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d169388, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16660, d169388, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14997 q = 1) (hb : d128484 q = 1) : d14997 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15007 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16661 q = 1) (hb : d169388 q = 1) : d14998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16661, d169388, d14998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16661, d169388, d14998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16662 q = 1) (hb : d169388 q = 1) : d14999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d14999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16662, d14999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55145 (p : Pattern) (ha : d16667 p = 1) (hb : d169388 p = 1) : d15009 p = 1 := by
  have h0 (q : Pattern) (ha : d13163 q = 1) (hb : d128484 q = 1) : d13163 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16666 q = 1) (hb : d169388 q = 1) : d15003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d169388, d15003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16666, d169388, d15003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15008 q = 1) (hb : d169388 q = 1) : d15008 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16667 q = 1) (hb : d169388 q = 1) : d15009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d15009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16667, d15009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55146 (p : Pattern) (ha : d16681 p = 1) (hb : d169388 p = 1) : d15030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d169388 q = 1) : d15000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d15000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55143 q ha hb
    | true =>
      simp only [d16663, d15000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55144 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d169388 q = 1) : d15001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d15001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d15001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d169388 q = 1) : d15002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d15002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d15002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d169388 q = 1) : d15010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d15010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55144 q ha hb
    | true =>
      simp only [d16668, d15010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55145 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d169388 q = 1) : d15011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d15011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d15011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d169388 q = 1) : d15012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d15012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d15012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d169388 q = 1) : d15013 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d169388 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55144 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d169388 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d169388 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15024 q = 1) (hb : d169388 q = 1) : d15024 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16676 q = 1) (hb : d169388 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16677 q = 1) (hb : d169388 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16678 q = 1) (hb : d169388 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16679 q = 1) (hb : d169388 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16680 q = 1) (hb : d169388 q = 1) : d15029 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16681 q = 1) (hb : d169388 q = 1) : d15030 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16681, d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16681, d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55147 (p : Pattern) (ha : d16686 p = 1) (hb : d169388 p = 1) : d15035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d169388 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55144 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d169388 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d169388 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15024 q = 1) (hb : d169388 q = 1) : d15024 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16676 q = 1) (hb : d169388 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d169388 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d169388 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d169388 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16684 q = 1) (hb : d169388 q = 1) : d15033 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16684, d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16685 q = 1) (hb : d169388 q = 1) : d15034 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16685, d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16686 q = 1) (hb : d169388 q = 1) : d15035 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16686, d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16686, d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55148 (p : Pattern) (ha : d16692 p = 1) (hb : d169388 p = 1) : d15041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16682 q = 1) (hb : d169388 q = 1) : d15031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16682, d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55146 q ha hb
    | true =>
      simp only [d16682, d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16683 q = 1) (hb : d169388 q = 1) : d15032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16683, d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16683, d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16687 q = 1) (hb : d169388 q = 1) : d15036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55147 q ha hb
    | true =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16688 q = 1) (hb : d169388 q = 1) : d15037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16689 q = 1) (hb : d169388 q = 1) : d15038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16689, d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16689, d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16690 q = 1) (hb : d169388 q = 1) : d15039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16690, d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16690, d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16691 q = 1) (hb : d169388 q = 1) : d15040 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16691, d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16691, d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16692 q = 1) (hb : d169388 q = 1) : d15041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16692, d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16692, d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55149 (p : Pattern) (ha : d16704 p = 1) (hb : d169388 p = 1) : d15054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16687 q = 1) (hb : d169388 q = 1) : d15036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55147 q ha hb
    | true =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16688 q = 1) (hb : d169388 q = 1) : d15037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d169388 q = 1) : d15049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55120 q ha hb
    | true =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d169388 q = 1) : d15050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16701 q = 1) (hb : d169388 q = 1) : d15051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16701, d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16701, d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16702 q = 1) (hb : d169388 q = 1) : d15052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16702, d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16702, d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16703 q = 1) (hb : d169388 q = 1) : d15053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16703, d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16703, d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16704 q = 1) (hb : d169388 q = 1) : d15054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16704, d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16704, d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55150 (p : Pattern) (ha : d16748 p = 1) (hb : d169388 p = 1) : d15111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d169388 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55144 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d169388 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d169388 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15024 q = 1) (hb : d169388 q = 1) : d15024 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16676 q = 1) (hb : d169388 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d169388 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d169388 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d169388 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d169388 q = 1) : d13190 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16743 q = 1) (hb : d169388 q = 1) : d15106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d15106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55119 q ha hb
    | true =>
      simp only [d16743, d15106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16744 q = 1) (hb : d169388 q = 1) : d15107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d15107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d15107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16745 q = 1) (hb : d169388 q = 1) : d15108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d15108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d15108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16746 q = 1) (hb : d169388 q = 1) : d15109 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16746, d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16747 q = 1) (hb : d169388 q = 1) : d15110 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16747, d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16748 q = 1) (hb : d169388 q = 1) : d15111 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16748, d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16748, d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55151 (p : Pattern) (ha : d16754 p = 1) (hb : d169388 p = 1) : d15117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16749 q = 1) (hb : d169388 q = 1) : d15112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16749, d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55150 q ha hb
    | true =>
      simp only [d16749, d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16750 q = 1) (hb : d169388 q = 1) : d15113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16750, d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16750, d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16751 q = 1) (hb : d169388 q = 1) : d15114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16751, d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16751, d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16752 q = 1) (hb : d169388 q = 1) : d15115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16752, d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16752, d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16753 q = 1) (hb : d169388 q = 1) : d15116 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16753, d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16753, d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16754 q = 1) (hb : d169388 q = 1) : d15117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16754, d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16754, d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55152 (p : Pattern) (ha : d128337 p = 1) (hb : d169388 p = 1) : d125597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16705 q = 1) (hb : d169388 q = 1) : d15055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16705, d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55148 q ha hb
    | true =>
      simp only [d16705, d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55149 q ha hb
  have h2 (q : Pattern) (ha : d128333 q = 1) (hb : d169388 q = 1) : d125593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128333, d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16755 q = 1) (hb : d169388 q = 1) : d15118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16755, d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55151 q ha hb
    | true =>
      simp only [d16755, d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16756 q = 1) (hb : d169388 q = 1) : d15119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16756, d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16756, d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d169388 q = 1) : d125594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128334, d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d169388 q = 1) : d125595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d169388 q = 1) : d125596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d169388 q = 1) : d125597 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55153 (p : Pattern) (ha : d128343 p = 1) (hb : d169388 p = 1) : d125603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16477 q = 1) (hb : d169388 q = 1) : d14805 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16477, d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16477, d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55110 q ha hb
  have h2 (q : Pattern) (ha : d16478 q = 1) (hb : d169388 q = 1) : d14806 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16478, d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16478, d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16487 q = 1) (hb : d169388 q = 1) : d14815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55110 q ha hb
    | true =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55113 q ha hb
  have h4 (q : Pattern) (ha : d16488 q = 1) (hb : d169388 q = 1) : d14816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16489 q = 1) (hb : d169388 q = 1) : d14817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16489, d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16489, d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128321 q = 1) (hb : d169388 q = 1) : d125581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128321, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55133 q ha hb
    | true =>
      simp only [d128321, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55141 q ha hb
  have h7 (q : Pattern) (ha : d16635 q = 1) (hb : d169388 q = 1) : d14972 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16635, d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55116 q ha hb
    | true =>
      simp only [d16635, d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55117 q ha hb
  have h8 (q : Pattern) (ha : d128322 q = 1) (hb : d169388 q = 1) : d125582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128322, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128322, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128323 q = 1) (hb : d169388 q = 1) : d125583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128323, d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128324 q = 1) (hb : d169388 q = 1) : d125584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128324, d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128328 q = 1) (hb : d169388 q = 1) : d125588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128328, d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55142 q ha hb
  have h12 (q : Pattern) (ha : d16644 q = 1) (hb : d169388 q = 1) : d14981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16644, d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16644, d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55118 q ha hb
  have h13 (q : Pattern) (ha : d128329 q = 1) (hb : d169388 q = 1) : d125589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128329, d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128330 q = 1) (hb : d169388 q = 1) : d125590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128330, d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128331 q = 1) (hb : d169388 q = 1) : d125591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128331, d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128332 q = 1) (hb : d169388 q = 1) : d125592 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128332, d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128338 q = 1) (hb : d169388 q = 1) : d125598 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128338, d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55152 q ha hb
  have h18 (q : Pattern) (ha : d16772 q = 1) (hb : d169388 q = 1) : d15135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16772, d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16772, d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55122 q ha hb
  have h19 (q : Pattern) (ha : d128339 q = 1) (hb : d169388 q = 1) : d125599 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128339, d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128340 q = 1) (hb : d169388 q = 1) : d125600 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128340, d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128341 q = 1) (hb : d169388 q = 1) : d125601 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128341, d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128342 q = 1) (hb : d169388 q = 1) : d125602 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128342, d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128343 q = 1) (hb : d169388 q = 1) : d125603 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128343, d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro55154 (p : Pattern) (ha : d128349 p = 1) (hb : d169388 p = 1) : d125609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d169388 q = 1) : d125604 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55153 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d169388 q = 1) : d125605 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d169388 q = 1) : d125606 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d169388 q = 1) : d125607 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d169388 q = 1) : d125608 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d169388 q = 1) : d125609 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55155 (p : Pattern) (ha : d16791 p = 1) (hb : d169388 p = 1) : d15154 p = 1 := by
  have h0 (q : Pattern) (ha : d1558 q = 1) (hb : d128484 q = 1) : d1558 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16788 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16789 q = 1) (hb : d169388 q = 1) : d15150 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d169388, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16789, d169388, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15152 q = 1) (hb : d128484 q = 1) : d15152 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16790 q = 1) (hb : d169388 q = 1) : d15153 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, d169388, d15153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16790, d169388, d15153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16791 q = 1) (hb : d169388 q = 1) : d15154 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d15154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16791, d15154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55156 (p : Pattern) (ha : d16795 p = 1) (hb : d169388 p = 1) : d15159 p = 1 := by
  have h0 (q : Pattern) (ha : d1573 q = 1) (hb : d128484 q = 1) : d1573 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16794 q = 1) (hb : d169388 q = 1) : d15155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d169388, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16794, d169388, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15158 q = 1) (hb : d169388 q = 1) : d15158 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16795 q = 1) (hb : d169388 q = 1) : d15159 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d15159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16795, d15159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55157 (p : Pattern) (ha : d16808 p = 1) (hb : d169388 p = 1) : d15177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d169388 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55155 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d169388 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d169388 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15166 q = 1) (hb : d169388 q = 1) : d15166 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d169388 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16800 q = 1) (hb : d169388 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16801 q = 1) (hb : d169388 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16802 q = 1) (hb : d169388 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15171 q = 1) (hb : d169388 q = 1) : d15171 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16803 q = 1) (hb : d169388 q = 1) : d15172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
    | true =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16804 q = 1) (hb : d169388 q = 1) : d15173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16805 q = 1) (hb : d169388 q = 1) : d15174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16806 q = 1) (hb : d169388 q = 1) : d15175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16807 q = 1) (hb : d169388 q = 1) : d15176 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16807, d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16808 q = 1) (hb : d169388 q = 1) : d15177 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16808, d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55158 (p : Pattern) (ha : d16812 p = 1) (hb : d169388 p = 1) : d15181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15171 q = 1) (hb : d169388 q = 1) : d15171 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16803 q = 1) (hb : d169388 q = 1) : d15172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
    | true =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16804 q = 1) (hb : d169388 q = 1) : d15173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16805 q = 1) (hb : d169388 q = 1) : d15174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16806 q = 1) (hb : d169388 q = 1) : d15175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16811 q = 1) (hb : d169388 q = 1) : d15180 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16811, d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16812 q = 1) (hb : d169388 q = 1) : d15181 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16812, d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55159 (p : Pattern) (ha : d16818 p = 1) (hb : d169388 p = 1) : d15187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d169388 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55157 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d169388 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d169388 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d169388 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d169388 q = 1) : d15186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16818 q = 1) (hb : d169388 q = 1) : d15187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16818, d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16818, d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55160 (p : Pattern) (ha : d16822 p = 1) (hb : d169388 p = 1) : d15191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d169388 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d169388 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d169388 q = 1) : d15190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16822 q = 1) (hb : d169388 q = 1) : d15191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16822, d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16822, d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55161 (p : Pattern) (ha : d16828 p = 1) (hb : d169388 p = 1) : d15197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d169388 q = 1) : d15192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55159 q ha hb
    | true =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55160 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d169388 q = 1) : d15193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d169388 q = 1) : d15194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d169388 q = 1) : d15195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d169388 q = 1) : d15196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16828 q = 1) (hb : d169388 q = 1) : d15197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16828, d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16828, d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55162 (p : Pattern) (ha : d16831 p = 1) (hb : d169388 p = 1) : d15200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d169388 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55157 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d169388 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d169388 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d169388 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d169388 q = 1) : d15186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16831 q = 1) (hb : d169388 q = 1) : d15200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16831, d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16831, d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55163 (p : Pattern) (ha : d16832 p = 1) (hb : d169388 p = 1) : d15201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d169388 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d169388 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d169388 q = 1) : d15190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16832 q = 1) (hb : d169388 q = 1) : d15201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16832, d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16832, d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55164 (p : Pattern) (ha : d16838 p = 1) (hb : d169388 p = 1) : d15207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d169388 q = 1) : d15192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55159 q ha hb
    | true =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55160 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d169388 q = 1) : d15193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d169388 q = 1) : d15194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d169388 q = 1) : d15195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d169388 q = 1) : d15196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16833 q = 1) (hb : d169388 q = 1) : d15202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55162 q ha hb
    | true =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55163 q ha hb
  have h7 (q : Pattern) (ha : d16834 q = 1) (hb : d169388 q = 1) : d15203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16835 q = 1) (hb : d169388 q = 1) : d15204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16836 q = 1) (hb : d169388 q = 1) : d15205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16837 q = 1) (hb : d169388 q = 1) : d15206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16838 q = 1) (hb : d169388 q = 1) : d15207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16838, d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16838, d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55165 (p : Pattern) (ha : d16879 p = 1) (hb : d169388 p = 1) : d15248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d169388 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55155 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d169388 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d169388 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15166 q = 1) (hb : d169388 q = 1) : d15166 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d169388 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16800 q = 1) (hb : d169388 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16801 q = 1) (hb : d169388 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16802 q = 1) (hb : d169388 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16877 q = 1) (hb : d169388 q = 1) : d15246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16877, d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16878 q = 1) (hb : d169388 q = 1) : d15247 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16878, d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16879 q = 1) (hb : d169388 q = 1) : d15248 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16879, d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16879, d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55166 (p : Pattern) (ha : d16889 p = 1) (hb : d169388 p = 1) : d15258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d169388 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55165 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d169388 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d169388 q = 1) : d15255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d169388 q = 1) : d15256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d169388 q = 1) : d15257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16889 q = 1) (hb : d169388 q = 1) : d15258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16889, d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16889, d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55167 (p : Pattern) (ha : d16983 p = 1) (hb : d169388 p = 1) : d15358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16973 q = 1) (hb : d169388 q = 1) : d15348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16973, d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55166 q ha hb
    | true =>
      simp only [d16973, d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55160 q ha hb
  have h2 (q : Pattern) (ha : d16974 q = 1) (hb : d169388 q = 1) : d15349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16974, d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16974, d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16975 q = 1) (hb : d169388 q = 1) : d15350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16975, d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16975, d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16976 q = 1) (hb : d169388 q = 1) : d15351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16976, d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16976, d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16977 q = 1) (hb : d169388 q = 1) : d15352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16977, d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16977, d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16978 q = 1) (hb : d169388 q = 1) : d15353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55160 q ha hb
    | true =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16979 q = 1) (hb : d169388 q = 1) : d15354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16980 q = 1) (hb : d169388 q = 1) : d15355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16981 q = 1) (hb : d169388 q = 1) : d15356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16982 q = 1) (hb : d169388 q = 1) : d15357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16983 q = 1) (hb : d169388 q = 1) : d15358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16983, d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16983, d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55168 (p : Pattern) (ha : d16989 p = 1) (hb : d169388 p = 1) : d15364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16978 q = 1) (hb : d169388 q = 1) : d15353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55160 q ha hb
    | true =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16979 q = 1) (hb : d169388 q = 1) : d15354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16980 q = 1) (hb : d169388 q = 1) : d15355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16981 q = 1) (hb : d169388 q = 1) : d15356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16982 q = 1) (hb : d169388 q = 1) : d15357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16984 q = 1) (hb : d169388 q = 1) : d15359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55163 q ha hb
    | true =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16985 q = 1) (hb : d169388 q = 1) : d15360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16986 q = 1) (hb : d169388 q = 1) : d15361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16987 q = 1) (hb : d169388 q = 1) : d15362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16988 q = 1) (hb : d169388 q = 1) : d15363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16989 q = 1) (hb : d169388 q = 1) : d15364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16989, d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16989, d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55169 (p : Pattern) (ha : d16998 p = 1) (hb : d169388 p = 1) : d15373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16984 q = 1) (hb : d169388 q = 1) : d15359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55163 q ha hb
    | true =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16985 q = 1) (hb : d169388 q = 1) : d15360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16986 q = 1) (hb : d169388 q = 1) : d15361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16987 q = 1) (hb : d169388 q = 1) : d15362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16988 q = 1) (hb : d169388 q = 1) : d15363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16998 q = 1) (hb : d169388 q = 1) : d15373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16998, d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16998, d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55170 (p : Pattern) (ha : d17032 p = 1) (hb : d169388 p = 1) : d15408 p = 1 := by
  have h0 (q : Pattern) (ha : d1865 q = 1) (hb : d128484 q = 1) : d1865 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17031 q = 1) (hb : d169388 q = 1) : d15407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d169388, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17031, d169388, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15401 q = 1) (hb : d169388 q = 1) : d15401 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17032 q = 1) (hb : d169388 q = 1) : d15408 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d15408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17032, d15408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55171 (p : Pattern) (ha : d17058 p = 1) (hb : d169388 p = 1) : d15441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15435 q = 1) (hb : d169388 q = 1) : d15435 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17053 q = 1) (hb : d169388 q = 1) : d15436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
    | true =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17054 q = 1) (hb : d169388 q = 1) : d15437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17055 q = 1) (hb : d169388 q = 1) : d15438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17056 q = 1) (hb : d169388 q = 1) : d15439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17057 q = 1) (hb : d169388 q = 1) : d15440 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17057, d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17058 q = 1) (hb : d169388 q = 1) : d15441 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17058, d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17058, d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55172 (p : Pattern) (ha : d17130 p = 1) (hb : d169388 p = 1) : d15521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17059 q = 1) (hb : d169388 q = 1) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55171 q ha hb
    | true =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17060 q = 1) (hb : d169388 q = 1) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17127 q = 1) (hb : d169388 q = 1) : d15518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17127, d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17127, d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17128 q = 1) (hb : d169388 q = 1) : d15519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17128, d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17128, d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17129 q = 1) (hb : d169388 q = 1) : d15520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17129, d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17129, d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17130 q = 1) (hb : d169388 q = 1) : d15521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17130, d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17130, d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55173 (p : Pattern) (ha : d17136 p = 1) (hb : d169388 p = 1) : d15527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17131 q = 1) (hb : d169388 q = 1) : d15522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17131, d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55172 q ha hb
    | true =>
      simp only [d17131, d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17132 q = 1) (hb : d169388 q = 1) : d15523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17132, d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17132, d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17133 q = 1) (hb : d169388 q = 1) : d15524 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17133, d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17133, d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17134 q = 1) (hb : d169388 q = 1) : d15525 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17134, d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17134, d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17135 q = 1) (hb : d169388 q = 1) : d15526 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17135, d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17135, d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17136 q = 1) (hb : d169388 q = 1) : d15527 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17136, d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17136, d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55174 (p : Pattern) (ha : d16843 p = 1) (hb : d169388 p = 1) : d15212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d169388 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55157 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d169388 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d169388 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d169388 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d169388 q = 1) : d15211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16843 q = 1) (hb : d169388 q = 1) : d15212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16843, d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16843, d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55175 (p : Pattern) (ha : d16845 p = 1) (hb : d169388 p = 1) : d15214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d169388 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d169388 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d169388 q = 1) : d15213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16845 q = 1) (hb : d169388 q = 1) : d15214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16845, d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16845, d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55176 (p : Pattern) (ha : d16852 p = 1) (hb : d169388 p = 1) : d15221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d169388 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55157 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d169388 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d169388 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d169388 q = 1) : d15219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d169388 q = 1) : d15220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16852 q = 1) (hb : d169388 q = 1) : d15221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16852, d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16852, d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55177 (p : Pattern) (ha : d16855 p = 1) (hb : d169388 p = 1) : d15224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d169388 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d169388 q = 1) : d15222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d169388 q = 1) : d15223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16855 q = 1) (hb : d169388 q = 1) : d15224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16855, d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16855, d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55178 (p : Pattern) (ha : d16863 p = 1) (hb : d169388 p = 1) : d15232 p = 1 := by
  have h0 (q : Pattern) (ha : d1668 q = 1) (hb : d128484 q = 1) : d1668 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16861 q = 1) (hb : d169388 q = 1) : d15228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d169388, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16861, d169388, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15230 q = 1) (hb : d128484 q = 1) : d15230 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16862 q = 1) (hb : d169388 q = 1) : d15231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16862, d169388, d15231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16862, d169388, d15231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16863 q = 1) (hb : d169388 q = 1) : d15232 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d15232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16863, d15232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55179 (p : Pattern) (ha : d16868 p = 1) (hb : d169388 p = 1) : d15237 p = 1 := by
  have h0 (q : Pattern) (ha : d13349 q = 1) (hb : d128484 q = 1) : d13349 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15157 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16867 q = 1) (hb : d169388 q = 1) : d15236 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d169388, d15236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16867, d169388, d15236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15158 q = 1) (hb : d169388 q = 1) : d15158 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16868 q = 1) (hb : d169388 q = 1) : d15237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d15237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16868, d15237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55180 (p : Pattern) (ha : d16874 p = 1) (hb : d169388 p = 1) : d15243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d169388 q = 1) : d15233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d15233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55178 q ha hb
    | true =>
      simp only [d16864, d15233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55155 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d169388 q = 1) : d15234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d15234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d15234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d169388 q = 1) : d15235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d15235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d15235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d169388 q = 1) : d15238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d15238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55155 q ha hb
    | true =>
      simp only [d16869, d15238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55179 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d169388 q = 1) : d15239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d15239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d15239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d169388 q = 1) : d15240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d15240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d15240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d169388 q = 1) : d15241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d169388 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55155 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d169388 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d169388 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15166 q = 1) (hb : d169388 q = 1) : d15166 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16799 q = 1) (hb : d169388 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16800 q = 1) (hb : d169388 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16801 q = 1) (hb : d169388 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16802 q = 1) (hb : d169388 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16873 q = 1) (hb : d169388 q = 1) : d15242 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16874 q = 1) (hb : d169388 q = 1) : d15243 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16874, d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16874, d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55181 (p : Pattern) (ha : d16885 p = 1) (hb : d169388 p = 1) : d15254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d169388 q = 1) : d15244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55180 q ha hb
    | true =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d169388 q = 1) : d15245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d169388 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55165 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d169388 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d169388 q = 1) : d15251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d169388 q = 1) : d15252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d169388 q = 1) : d15253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16885 q = 1) (hb : d169388 q = 1) : d15254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16885, d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16885, d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55182 (p : Pattern) (ha : d16934 p = 1) (hb : d169388 p = 1) : d15309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d169388 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55155 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d169388 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d169388 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15166 q = 1) (hb : d169388 q = 1) : d15166 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d169388 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16800 q = 1) (hb : d169388 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16801 q = 1) (hb : d169388 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16802 q = 1) (hb : d169388 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13287 q = 1) (hb : d169388 q = 1) : d13287 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16929 q = 1) (hb : d169388 q = 1) : d15304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d15304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55156 q ha hb
    | true =>
      simp only [d16929, d15304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16930 q = 1) (hb : d169388 q = 1) : d15305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16930, d15305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16930, d15305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16931 q = 1) (hb : d169388 q = 1) : d15306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16931, d15306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16931, d15306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16932 q = 1) (hb : d169388 q = 1) : d15307 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16932, d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16932, d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16933 q = 1) (hb : d169388 q = 1) : d15308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16933, d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16933, d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16934 q = 1) (hb : d169388 q = 1) : d15309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16934, d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16934, d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55183 (p : Pattern) (ha : d16940 p = 1) (hb : d169388 p = 1) : d15315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d169388 q = 1) : d15310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55182 q ha hb
    | true =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d169388 q = 1) : d15311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d169388 q = 1) : d15312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d169388 q = 1) : d15313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d169388 q = 1) : d15314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16940 q = 1) (hb : d169388 q = 1) : d15315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16940, d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16940, d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55184 (p : Pattern) (ha : d128357 p = 1) (hb : d169388 p = 1) : d125617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d169388 q = 1) : d15215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55174 q ha hb
    | true =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55175 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d169388 q = 1) : d15216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d169388 q = 1) : d15217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d169388 q = 1) : d15218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d169388 q = 1) : d15225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55176 q ha hb
    | true =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55177 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d169388 q = 1) : d15226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d169388 q = 1) : d15227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d169388 q = 1) : d15259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55181 q ha hb
    | true =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55166 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d169388 q = 1) : d125613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d169388 q = 1) : d15316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55183 q ha hb
    | true =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d169388 q = 1) : d15317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d169388 q = 1) : d125614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d169388 q = 1) : d125615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d169388 q = 1) : d125616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128357 q = 1) (hb : d169388 q = 1) : d125617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128357, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128357, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55185 (p : Pattern) (ha : d16947 p = 1) (hb : d169388 p = 1) : d15322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d169388 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55157 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d169388 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d169388 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d169388 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d169388 q = 1) : d15211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16947 q = 1) (hb : d169388 q = 1) : d15322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16947, d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16947, d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55186 (p : Pattern) (ha : d16948 p = 1) (hb : d169388 p = 1) : d15323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d169388 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d169388 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d169388 q = 1) : d15213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16948 q = 1) (hb : d169388 q = 1) : d15323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16948, d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16948, d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55187 (p : Pattern) (ha : d16953 p = 1) (hb : d169388 p = 1) : d15328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d169388 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55157 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d169388 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d169388 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d169388 q = 1) : d15219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d169388 q = 1) : d15220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16953 q = 1) (hb : d169388 q = 1) : d15328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16953, d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16953, d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55188 (p : Pattern) (ha : d16954 p = 1) (hb : d169388 p = 1) : d15329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d169388 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d169388 q = 1) : d15222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d169388 q = 1) : d15223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16954 q = 1) (hb : d169388 q = 1) : d15329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16954, d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16954, d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55189 (p : Pattern) (ha : d16958 p = 1) (hb : d169388 p = 1) : d15333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d169388 q = 1) : d15244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55180 q ha hb
    | true =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d169388 q = 1) : d15245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d169388 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55165 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d169388 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d169388 q = 1) : d15251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d169388 q = 1) : d15252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d169388 q = 1) : d15253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16958 q = 1) (hb : d169388 q = 1) : d15333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16958, d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16958, d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55190 (p : Pattern) (ha : d16959 p = 1) (hb : d169388 p = 1) : d15334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d169388 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55165 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d169388 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d169388 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55158 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d169388 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d169388 q = 1) : d15255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d169388 q = 1) : d15256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d169388 q = 1) : d15257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16959 q = 1) (hb : d169388 q = 1) : d15334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16959, d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16959, d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55191 (p : Pattern) (ha : d16965 p = 1) (hb : d169388 p = 1) : d15340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d169388 q = 1) : d15310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55182 q ha hb
    | true =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d169388 q = 1) : d15311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d169388 q = 1) : d15312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d169388 q = 1) : d15313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d169388 q = 1) : d15314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16965 q = 1) (hb : d169388 q = 1) : d15340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16965, d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16965, d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55192 (p : Pattern) (ha : d128362 p = 1) (hb : d169388 p = 1) : d125622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d169388 q = 1) : d15215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55174 q ha hb
    | true =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55175 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d169388 q = 1) : d15216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d169388 q = 1) : d15217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d169388 q = 1) : d15218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d169388 q = 1) : d15225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55176 q ha hb
    | true =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55177 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d169388 q = 1) : d15226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d169388 q = 1) : d15227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d169388 q = 1) : d15259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55181 q ha hb
    | true =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55166 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d169388 q = 1) : d125613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d169388 q = 1) : d15316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55183 q ha hb
    | true =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d169388 q = 1) : d15317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d169388 q = 1) : d125614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d169388 q = 1) : d125615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d169388 q = 1) : d125616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16949 q = 1) (hb : d169388 q = 1) : d15324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16949, d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55185 q ha hb
    | true =>
      simp only [d16949, d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55186 q ha hb
  have h16 (q : Pattern) (ha : d16950 q = 1) (hb : d169388 q = 1) : d15325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16950, d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16950, d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16951 q = 1) (hb : d169388 q = 1) : d15326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16951, d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16951, d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16952 q = 1) (hb : d169388 q = 1) : d15327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16952, d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16952, d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16955 q = 1) (hb : d169388 q = 1) : d15330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16955, d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55187 q ha hb
    | true =>
      simp only [d16955, d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55188 q ha hb
  have h20 (q : Pattern) (ha : d16956 q = 1) (hb : d169388 q = 1) : d15331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16956, d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16956, d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16957 q = 1) (hb : d169388 q = 1) : d15332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16957, d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16957, d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16960 q = 1) (hb : d169388 q = 1) : d15335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55189 q ha hb
    | true =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55190 q ha hb
  have h23 (q : Pattern) (ha : d128358 q = 1) (hb : d169388 q = 1) : d125618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16966 q = 1) (hb : d169388 q = 1) : d15341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55191 q ha hb
    | true =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16967 q = 1) (hb : d169388 q = 1) : d15342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128359 q = 1) (hb : d169388 q = 1) : d125619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128360 q = 1) (hb : d169388 q = 1) : d125620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128360, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128360, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128361 q = 1) (hb : d169388 q = 1) : d125621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128361, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128361, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128362 q = 1) (hb : d169388 q = 1) : d125622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128362, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128362, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro55193 (p : Pattern) (ha : d128369 p = 1) (hb : d169388 p = 1) : d125629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16960 q = 1) (hb : d169388 q = 1) : d15335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55189 q ha hb
    | true =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55190 q ha hb
  have h2 (q : Pattern) (ha : d128358 q = 1) (hb : d169388 q = 1) : d125618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16966 q = 1) (hb : d169388 q = 1) : d15341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55191 q ha hb
    | true =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16967 q = 1) (hb : d169388 q = 1) : d15342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128359 q = 1) (hb : d169388 q = 1) : d125619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128367 q = 1) (hb : d169388 q = 1) : d125627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128367, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128367, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128368 q = 1) (hb : d169388 q = 1) : d125628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128368, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128368, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d169388 q = 1) : d125629 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55194 (p : Pattern) (ha : d17010 p = 1) (hb : d169388 p = 1) : d15385 p = 1 := by
  have h0 (q : Pattern) (ha : d1856 q = 1) (hb : d128484 q = 1) : d1856 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17008 q = 1) (hb : d169388 q = 1) : d15379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d169388, d15379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17008, d169388, d15379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15383 q = 1) (hb : d128484 q = 1) : d15383 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15390 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17009 q = 1) (hb : d169388 q = 1) : d15384 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17009, d169388, d15384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17009, d169388, d15384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17010 q = 1) (hb : d169388 q = 1) : d15385 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d15385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17010, d15385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55195 (p : Pattern) (ha : d17017 p = 1) (hb : d169388 p = 1) : d15392 p = 1 := by
  have h0 (q : Pattern) (ha : d1860 q = 1) (hb : d128484 q = 1) : d1860 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17015 q = 1) (hb : d169388 q = 1) : d15386 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d169388, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17015, d169388, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15390 q = 1) (hb : d128484 q = 1) : d15390 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17016 q = 1) (hb : d169388 q = 1) : d15391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17016, d169388, d15391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17016, d169388, d15391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17017 q = 1) (hb : d169388 q = 1) : d15392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d15392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17017, d15392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55196 (p : Pattern) (ha : d17022 p = 1) (hb : d169388 p = 1) : d15402 p = 1 := by
  have h0 (q : Pattern) (ha : d13489 q = 1) (hb : d128484 q = 1) : d13489 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17021 q = 1) (hb : d169388 q = 1) : d15396 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d169388, d15396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17021, d169388, d15396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15401 q = 1) (hb : d169388 q = 1) : d15401 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17022 q = 1) (hb : d169388 q = 1) : d15402 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d15402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17022, d15402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55197 (p : Pattern) (ha : d17041 p = 1) (hb : d169388 p = 1) : d15423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d169388 q = 1) : d15393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d15393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55194 q ha hb
    | true =>
      simp only [d17018, d15393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55195 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d169388 q = 1) : d15394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d15394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d15394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d169388 q = 1) : d15395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d15395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d15395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d169388 q = 1) : d15403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d15403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55195 q ha hb
    | true =>
      simp only [d17023, d15403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55196 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d169388 q = 1) : d15404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d15404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d15404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d169388 q = 1) : d15405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d15405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d15405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d169388 q = 1) : d15406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d169388 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55195 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d169388 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d169388 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15417 q = 1) (hb : d169388 q = 1) : d15417 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17036 q = 1) (hb : d169388 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17037 q = 1) (hb : d169388 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17038 q = 1) (hb : d169388 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17039 q = 1) (hb : d169388 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17040 q = 1) (hb : d169388 q = 1) : d15422 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17041 q = 1) (hb : d169388 q = 1) : d15423 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17041, d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17041, d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55198 (p : Pattern) (ha : d17046 p = 1) (hb : d169388 p = 1) : d15428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d169388 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55195 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d169388 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d169388 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15417 q = 1) (hb : d169388 q = 1) : d15417 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17036 q = 1) (hb : d169388 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d169388 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d169388 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d169388 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17044 q = 1) (hb : d169388 q = 1) : d15426 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17044, d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17045 q = 1) (hb : d169388 q = 1) : d15427 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17045, d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17046 q = 1) (hb : d169388 q = 1) : d15428 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17046, d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17046, d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55199 (p : Pattern) (ha : d17052 p = 1) (hb : d169388 p = 1) : d15434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17042 q = 1) (hb : d169388 q = 1) : d15424 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17042, d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55197 q ha hb
    | true =>
      simp only [d17042, d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17043 q = 1) (hb : d169388 q = 1) : d15425 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17043, d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17043, d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17047 q = 1) (hb : d169388 q = 1) : d15429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55198 q ha hb
    | true =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17048 q = 1) (hb : d169388 q = 1) : d15430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17049 q = 1) (hb : d169388 q = 1) : d15431 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17049, d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17049, d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17050 q = 1) (hb : d169388 q = 1) : d15432 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17050, d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17050, d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17051 q = 1) (hb : d169388 q = 1) : d15433 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17051, d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17051, d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17052 q = 1) (hb : d169388 q = 1) : d15434 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17052, d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17052, d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55200 (p : Pattern) (ha : d17064 p = 1) (hb : d169388 p = 1) : d15447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17047 q = 1) (hb : d169388 q = 1) : d15429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55198 q ha hb
    | true =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17048 q = 1) (hb : d169388 q = 1) : d15430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d169388 q = 1) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55171 q ha hb
    | true =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d169388 q = 1) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17061 q = 1) (hb : d169388 q = 1) : d15444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17061, d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17061, d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17062 q = 1) (hb : d169388 q = 1) : d15445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17062, d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17062, d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17063 q = 1) (hb : d169388 q = 1) : d15446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17063, d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17063, d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17064 q = 1) (hb : d169388 q = 1) : d15447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17064, d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17064, d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55201 (p : Pattern) (ha : d17113 p = 1) (hb : d169388 p = 1) : d15504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d169388 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55195 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d169388 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d169388 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15417 q = 1) (hb : d169388 q = 1) : d15417 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17036 q = 1) (hb : d169388 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d169388 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d169388 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d169388 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13516 q = 1) (hb : d169388 q = 1) : d13516 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17108 q = 1) (hb : d169388 q = 1) : d15499 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d15499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55170 q ha hb
    | true =>
      simp only [d17108, d15499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17109 q = 1) (hb : d169388 q = 1) : d15500 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d15500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d15500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17110 q = 1) (hb : d169388 q = 1) : d15501 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d15501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d15501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17111 q = 1) (hb : d169388 q = 1) : d15502 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17111, d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17112 q = 1) (hb : d169388 q = 1) : d15503 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17112, d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17113 q = 1) (hb : d169388 q = 1) : d15504 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17113, d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17113, d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55202 (p : Pattern) (ha : d17119 p = 1) (hb : d169388 p = 1) : d15510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17114 q = 1) (hb : d169388 q = 1) : d15505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17114, d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55201 q ha hb
    | true =>
      simp only [d17114, d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17115 q = 1) (hb : d169388 q = 1) : d15506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17115, d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17115, d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17116 q = 1) (hb : d169388 q = 1) : d15507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17116, d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17116, d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17117 q = 1) (hb : d169388 q = 1) : d15508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17117, d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17117, d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17118 q = 1) (hb : d169388 q = 1) : d15509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17118, d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17118, d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17119 q = 1) (hb : d169388 q = 1) : d15510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17119, d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17119, d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55203 (p : Pattern) (ha : d128379 p = 1) (hb : d169388 p = 1) : d125639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17065 q = 1) (hb : d169388 q = 1) : d15448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17065, d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55199 q ha hb
    | true =>
      simp only [d17065, d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55200 q ha hb
  have h2 (q : Pattern) (ha : d128375 q = 1) (hb : d169388 q = 1) : d125635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128375, d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17120 q = 1) (hb : d169388 q = 1) : d15511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17120, d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55202 q ha hb
    | true =>
      simp only [d17120, d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17121 q = 1) (hb : d169388 q = 1) : d15512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17121, d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17121, d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d169388 q = 1) : d125636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128376, d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d169388 q = 1) : d125637 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d169388 q = 1) : d125638 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d169388 q = 1) : d125639 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55204 (p : Pattern) (ha : d128385 p = 1) (hb : d169388 p = 1) : d125645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16829 q = 1) (hb : d169388 q = 1) : d15198 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16829, d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16829, d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55161 q ha hb
  have h2 (q : Pattern) (ha : d16830 q = 1) (hb : d169388 q = 1) : d15199 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16830, d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16830, d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16839 q = 1) (hb : d169388 q = 1) : d15208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55161 q ha hb
    | true =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55164 q ha hb
  have h4 (q : Pattern) (ha : d16840 q = 1) (hb : d169388 q = 1) : d15209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16841 q = 1) (hb : d169388 q = 1) : d15210 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16841, d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16841, d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128363 q = 1) (hb : d169388 q = 1) : d125623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128363, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55184 q ha hb
    | true =>
      simp only [d128363, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55192 q ha hb
  have h7 (q : Pattern) (ha : d16990 q = 1) (hb : d169388 q = 1) : d15365 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16990, d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55167 q ha hb
    | true =>
      simp only [d16990, d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55168 q ha hb
  have h8 (q : Pattern) (ha : d128364 q = 1) (hb : d169388 q = 1) : d125624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128364, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128364, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128365 q = 1) (hb : d169388 q = 1) : d125625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128365, d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128366 q = 1) (hb : d169388 q = 1) : d125626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128366, d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128370 q = 1) (hb : d169388 q = 1) : d125630 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128370, d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55193 q ha hb
  have h12 (q : Pattern) (ha : d16999 q = 1) (hb : d169388 q = 1) : d15374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16999, d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16999, d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55169 q ha hb
  have h13 (q : Pattern) (ha : d128371 q = 1) (hb : d169388 q = 1) : d125631 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128371, d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128372 q = 1) (hb : d169388 q = 1) : d125632 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128372, d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128373 q = 1) (hb : d169388 q = 1) : d125633 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128373, d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128374 q = 1) (hb : d169388 q = 1) : d125634 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128374, d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128380 q = 1) (hb : d169388 q = 1) : d125640 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128380, d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55203 q ha hb
  have h18 (q : Pattern) (ha : d17137 q = 1) (hb : d169388 q = 1) : d15528 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17137, d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17137, d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55173 q ha hb
  have h19 (q : Pattern) (ha : d128381 q = 1) (hb : d169388 q = 1) : d125641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128381, d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128382 q = 1) (hb : d169388 q = 1) : d125642 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128382, d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128383 q = 1) (hb : d169388 q = 1) : d125643 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128383, d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128384 q = 1) (hb : d169388 q = 1) : d125644 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128384, d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128385 q = 1) (hb : d169388 q = 1) : d125645 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128385, d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro55205 (p : Pattern) (ha : d128391 p = 1) (hb : d169388 p = 1) : d125651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d169388 q = 1) : d125646 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55204 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d169388 q = 1) : d125647 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d169388 q = 1) : d125648 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d169388 q = 1) : d125649 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d169388 q = 1) : d125650 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d169388 q = 1) : d125651 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55206 (p : Pattern) (ha : d17157 p = 1) (hb : d169388 p = 1) : d15546 p = 1 := by
  have h0 (q : Pattern) (ha : d2038 q = 1) (hb : d128484 q = 1) : d2038 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17155 q = 1) (hb : d169388 q = 1) : d15544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d169388, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17155, d169388, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13676 q = 1) (hb : d128484 q = 1) : d13676 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15549 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17156 q = 1) (hb : d169388 q = 1) : d15545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d169388, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17156, d169388, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17157 q = 1) (hb : d169388 q = 1) : d15546 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, d15546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17157, d15546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55207 (p : Pattern) (ha : d17161 p = 1) (hb : d169388 p = 1) : d15551 p = 1 := by
  have h0 (q : Pattern) (ha : d2056 q = 1) (hb : d128484 q = 1) : d2056 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17160 q = 1) (hb : d169388 q = 1) : d15547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, d169388, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17160, d169388, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15550 q = 1) (hb : d169388 q = 1) : d15550 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17161 q = 1) (hb : d169388 q = 1) : d15551 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, d15551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17161, d15551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55208 (p : Pattern) (ha : d17174 p = 1) (hb : d169388 p = 1) : d15569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d169388 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55206 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d169388 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d169388 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15558 q = 1) (hb : d169388 q = 1) : d15558 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d169388 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17166 q = 1) (hb : d169388 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17167 q = 1) (hb : d169388 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17168 q = 1) (hb : d169388 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15563 q = 1) (hb : d169388 q = 1) : d15563 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17169 q = 1) (hb : d169388 q = 1) : d15564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
    | true =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17170 q = 1) (hb : d169388 q = 1) : d15565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17171 q = 1) (hb : d169388 q = 1) : d15566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17172 q = 1) (hb : d169388 q = 1) : d15567 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17173 q = 1) (hb : d169388 q = 1) : d15568 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17173, d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17173, d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17174 q = 1) (hb : d169388 q = 1) : d15569 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17174, d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17174, d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55209 (p : Pattern) (ha : d17178 p = 1) (hb : d169388 p = 1) : d15573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15563 q = 1) (hb : d169388 q = 1) : d15563 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17169 q = 1) (hb : d169388 q = 1) : d15564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
    | true =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17170 q = 1) (hb : d169388 q = 1) : d15565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17171 q = 1) (hb : d169388 q = 1) : d15566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17172 q = 1) (hb : d169388 q = 1) : d15567 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17177 q = 1) (hb : d169388 q = 1) : d15572 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17177, d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17177, d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17178 q = 1) (hb : d169388 q = 1) : d15573 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17178, d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17178, d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55210 (p : Pattern) (ha : d17184 p = 1) (hb : d169388 p = 1) : d15579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d169388 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55208 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d169388 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d169388 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d169388 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d169388 q = 1) : d15578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17184 q = 1) (hb : d169388 q = 1) : d15579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17184, d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17184, d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55211 (p : Pattern) (ha : d17188 p = 1) (hb : d169388 p = 1) : d15583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d169388 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d169388 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d169388 q = 1) : d15582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17188 q = 1) (hb : d169388 q = 1) : d15583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17188, d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17188, d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55212 (p : Pattern) (ha : d17194 p = 1) (hb : d169388 p = 1) : d15589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d169388 q = 1) : d15584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55210 q ha hb
    | true =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55211 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d169388 q = 1) : d15585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d169388 q = 1) : d15586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d169388 q = 1) : d15587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d169388 q = 1) : d15588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17194 q = 1) (hb : d169388 q = 1) : d15589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17194, d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17194, d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55213 (p : Pattern) (ha : d17197 p = 1) (hb : d169388 p = 1) : d15592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d169388 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55208 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d169388 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d169388 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d169388 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d169388 q = 1) : d15578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17197 q = 1) (hb : d169388 q = 1) : d15592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17197, d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17197, d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55214 (p : Pattern) (ha : d17198 p = 1) (hb : d169388 p = 1) : d15593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d169388 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d169388 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d169388 q = 1) : d15582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17198 q = 1) (hb : d169388 q = 1) : d15593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17198, d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17198, d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55215 (p : Pattern) (ha : d17204 p = 1) (hb : d169388 p = 1) : d15599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d169388 q = 1) : d15584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55210 q ha hb
    | true =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55211 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d169388 q = 1) : d15585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d169388 q = 1) : d15586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d169388 q = 1) : d15587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d169388 q = 1) : d15588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17199 q = 1) (hb : d169388 q = 1) : d15594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55213 q ha hb
    | true =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55214 q ha hb
  have h7 (q : Pattern) (ha : d17200 q = 1) (hb : d169388 q = 1) : d15595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17201 q = 1) (hb : d169388 q = 1) : d15596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17202 q = 1) (hb : d169388 q = 1) : d15597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17203 q = 1) (hb : d169388 q = 1) : d15598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17204 q = 1) (hb : d169388 q = 1) : d15599 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17204, d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17204, d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55216 (p : Pattern) (ha : d17244 p = 1) (hb : d169388 p = 1) : d15636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d169388 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55206 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d169388 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d169388 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15558 q = 1) (hb : d169388 q = 1) : d15558 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d169388 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17166 q = 1) (hb : d169388 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17167 q = 1) (hb : d169388 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17168 q = 1) (hb : d169388 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17242 q = 1) (hb : d169388 q = 1) : d15634 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17242, d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17242, d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17243 q = 1) (hb : d169388 q = 1) : d15635 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17243, d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17243, d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17244 q = 1) (hb : d169388 q = 1) : d15636 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17244, d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17244, d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro55217 (p : Pattern) (ha : d17254 p = 1) (hb : d169388 p = 1) : d15646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d169388 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55216 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d169388 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d169388 q = 1) : d15643 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d169388 q = 1) : d15644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d169388 q = 1) : d15645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17254 q = 1) (hb : d169388 q = 1) : d15646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17254, d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17254, d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55218 (p : Pattern) (ha : d17348 p = 1) (hb : d169388 p = 1) : d15746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17338 q = 1) (hb : d169388 q = 1) : d15736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17338, d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55217 q ha hb
    | true =>
      simp only [d17338, d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55211 q ha hb
  have h2 (q : Pattern) (ha : d17339 q = 1) (hb : d169388 q = 1) : d15737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17339, d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17339, d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17340 q = 1) (hb : d169388 q = 1) : d15738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17340, d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17340, d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17341 q = 1) (hb : d169388 q = 1) : d15739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17341, d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17341, d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17342 q = 1) (hb : d169388 q = 1) : d15740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17342, d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17342, d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17343 q = 1) (hb : d169388 q = 1) : d15741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55211 q ha hb
    | true =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17344 q = 1) (hb : d169388 q = 1) : d15742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17345 q = 1) (hb : d169388 q = 1) : d15743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17346 q = 1) (hb : d169388 q = 1) : d15744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17347 q = 1) (hb : d169388 q = 1) : d15745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17348 q = 1) (hb : d169388 q = 1) : d15746 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17348, d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17348, d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55219 (p : Pattern) (ha : d17354 p = 1) (hb : d169388 p = 1) : d15752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17343 q = 1) (hb : d169388 q = 1) : d15741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55211 q ha hb
    | true =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17344 q = 1) (hb : d169388 q = 1) : d15742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17345 q = 1) (hb : d169388 q = 1) : d15743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17346 q = 1) (hb : d169388 q = 1) : d15744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17347 q = 1) (hb : d169388 q = 1) : d15745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17349 q = 1) (hb : d169388 q = 1) : d15747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55214 q ha hb
    | true =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17350 q = 1) (hb : d169388 q = 1) : d15748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17351 q = 1) (hb : d169388 q = 1) : d15749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17352 q = 1) (hb : d169388 q = 1) : d15750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17353 q = 1) (hb : d169388 q = 1) : d15751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17354 q = 1) (hb : d169388 q = 1) : d15752 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17354, d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17354, d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55220 (p : Pattern) (ha : d17363 p = 1) (hb : d169388 p = 1) : d15761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17349 q = 1) (hb : d169388 q = 1) : d15747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55214 q ha hb
    | true =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17350 q = 1) (hb : d169388 q = 1) : d15748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17351 q = 1) (hb : d169388 q = 1) : d15749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17352 q = 1) (hb : d169388 q = 1) : d15750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17353 q = 1) (hb : d169388 q = 1) : d15751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17363 q = 1) (hb : d169388 q = 1) : d15761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17363, d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17363, d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55221 (p : Pattern) (ha : d17396 p = 1) (hb : d169388 p = 1) : d15786 p = 1 := by
  have h0 (q : Pattern) (ha : d2343 q = 1) (hb : d128484 q = 1) : d2343 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17395 q = 1) (hb : d169388 q = 1) : d15785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d169388, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17395, d169388, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15779 q = 1) (hb : d169388 q = 1) : d15779 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17396 q = 1) (hb : d169388 q = 1) : d15786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d15786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17396, d15786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55222 (p : Pattern) (ha : d17422 p = 1) (hb : d169388 p = 1) : d15819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15813 q = 1) (hb : d169388 q = 1) : d15813 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17417 q = 1) (hb : d169388 q = 1) : d15814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55221 q ha hb
    | true =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17418 q = 1) (hb : d169388 q = 1) : d15815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17419 q = 1) (hb : d169388 q = 1) : d15816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17420 q = 1) (hb : d169388 q = 1) : d15817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17421 q = 1) (hb : d169388 q = 1) : d15818 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17421, d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17422 q = 1) (hb : d169388 q = 1) : d15819 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17422, d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17422, d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro55223 (p : Pattern) (ha : d17494 p = 1) (hb : d169388 p = 1) : d15899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17423 q = 1) (hb : d169388 q = 1) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55222 q ha hb
    | true =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17424 q = 1) (hb : d169388 q = 1) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17491 q = 1) (hb : d169388 q = 1) : d15896 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17491, d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17491, d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17492 q = 1) (hb : d169388 q = 1) : d15897 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17492, d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17492, d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17493 q = 1) (hb : d169388 q = 1) : d15898 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17493, d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17493, d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17494 q = 1) (hb : d169388 q = 1) : d15899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17494, d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17494, d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55224 (p : Pattern) (ha : d17500 p = 1) (hb : d169388 p = 1) : d15905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17495 q = 1) (hb : d169388 q = 1) : d15900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17495, d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55223 q ha hb
    | true =>
      simp only [d17495, d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17496 q = 1) (hb : d169388 q = 1) : d15901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17496, d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17496, d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17497 q = 1) (hb : d169388 q = 1) : d15902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17497, d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17497, d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17498 q = 1) (hb : d169388 q = 1) : d15903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17498, d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17498, d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17499 q = 1) (hb : d169388 q = 1) : d15904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17499, d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17499, d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17500 q = 1) (hb : d169388 q = 1) : d15905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17500, d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17500, d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55225 (p : Pattern) (ha : d17209 p = 1) (hb : d169388 p = 1) : d15604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d169388 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55208 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d169388 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d169388 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d169388 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d169388 q = 1) : d15603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17209 q = 1) (hb : d169388 q = 1) : d15604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17209, d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17209, d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55226 (p : Pattern) (ha : d17211 p = 1) (hb : d169388 p = 1) : d15606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d169388 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d169388 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d169388 q = 1) : d15605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17211 q = 1) (hb : d169388 q = 1) : d15606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17211, d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17211, d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55227 (p : Pattern) (ha : d17218 p = 1) (hb : d169388 p = 1) : d15613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d169388 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55208 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d169388 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d169388 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d169388 q = 1) : d15611 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d169388 q = 1) : d15612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17218 q = 1) (hb : d169388 q = 1) : d15613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17218, d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17218, d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55228 (p : Pattern) (ha : d17221 p = 1) (hb : d169388 p = 1) : d15616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d169388 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d169388 q = 1) : d15614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d169388 q = 1) : d15615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17221 q = 1) (hb : d169388 q = 1) : d15616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17221, d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17221, d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55229 (p : Pattern) (ha : d17229 p = 1) (hb : d169388 p = 1) : d15621 p = 1 := by
  have h0 (q : Pattern) (ha : d2147 q = 1) (hb : d128484 q = 1) : d2147 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17226 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17227 q = 1) (hb : d169388 q = 1) : d15620 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, d169388, d15620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17227, d169388, d15620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128484 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13676 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17228 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d169388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17228, d169388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17229 q = 1) (hb : d169388 q = 1) : d15621 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17229, d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55230 (p : Pattern) (ha : d17233 p = 1) (hb : d169388 p = 1) : d15625 p = 1 := by
  have h0 (q : Pattern) (ha : d13676 q = 1) (hb : d128484 q = 1) : d13676 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17156 q = 1) (hb : d169388 q = 1) : d15545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d169388, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17156, d169388, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15550 q = 1) (hb : d169388 q = 1) : d15550 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17233 q = 1) (hb : d169388 q = 1) : d15625 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, d15625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17233, d15625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55231 (p : Pattern) (ha : d17239 p = 1) (hb : d169388 p = 1) : d15631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d169388 q = 1) : d15622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d15622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55229 q ha hb
    | true =>
      simp only [d17230, d15622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55206 q ha hb
  have h2 (q : Pattern) (ha : d17231 q = 1) (hb : d169388 q = 1) : d15623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17231, d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17231, d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17232 q = 1) (hb : d169388 q = 1) : d15624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17232, d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17232, d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d169388 q = 1) : d15626 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d15626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55206 q ha hb
    | true =>
      simp only [d17234, d15626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55230 q ha hb
  have h5 (q : Pattern) (ha : d17235 q = 1) (hb : d169388 q = 1) : d15627 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17235, d15627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17235, d15627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17236 q = 1) (hb : d169388 q = 1) : d15628 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17236, d15628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17236, d15628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17237 q = 1) (hb : d169388 q = 1) : d15629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17237, d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17237, d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d169388 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55206 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
  have h9 (q : Pattern) (ha : d17163 q = 1) (hb : d169388 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17164 q = 1) (hb : d169388 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15558 q = 1) (hb : d169388 q = 1) : d15558 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17165 q = 1) (hb : d169388 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17166 q = 1) (hb : d169388 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17167 q = 1) (hb : d169388 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17168 q = 1) (hb : d169388 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17238 q = 1) (hb : d169388 q = 1) : d15630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17238, d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17238, d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17239 q = 1) (hb : d169388 q = 1) : d15631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17239, d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17239, d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55232 (p : Pattern) (ha : d17250 p = 1) (hb : d169388 p = 1) : d15642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d169388 q = 1) : d15632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55231 q ha hb
    | true =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d169388 q = 1) : d15633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d169388 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55216 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d169388 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d169388 q = 1) : d15639 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d169388 q = 1) : d15640 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d169388 q = 1) : d15641 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17250 q = 1) (hb : d169388 q = 1) : d15642 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17250, d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17250, d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55233 (p : Pattern) (ha : d17299 p = 1) (hb : d169388 p = 1) : d15697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d169388 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55206 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d169388 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d169388 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15558 q = 1) (hb : d169388 q = 1) : d15558 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d169388 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17166 q = 1) (hb : d169388 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17167 q = 1) (hb : d169388 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17168 q = 1) (hb : d169388 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13614 q = 1) (hb : d169388 q = 1) : d13614 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17294 q = 1) (hb : d169388 q = 1) : d15692 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d15692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55207 q ha hb
    | true =>
      simp only [d17294, d15692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17295 q = 1) (hb : d169388 q = 1) : d15693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17295, d15693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17295, d15693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17296 q = 1) (hb : d169388 q = 1) : d15694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17296, d15694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17296, d15694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17297 q = 1) (hb : d169388 q = 1) : d15695 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17297, d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17297, d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17298 q = 1) (hb : d169388 q = 1) : d15696 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17298, d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17298, d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17299 q = 1) (hb : d169388 q = 1) : d15697 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17299, d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17299, d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro55234 (p : Pattern) (ha : d17305 p = 1) (hb : d169388 p = 1) : d15703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d169388 q = 1) : d15698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55233 q ha hb
    | true =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d169388 q = 1) : d15699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d169388 q = 1) : d15700 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d169388 q = 1) : d15701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d169388 q = 1) : d15702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17305 q = 1) (hb : d169388 q = 1) : d15703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17305, d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17305, d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55235 (p : Pattern) (ha : d128400 p = 1) (hb : d169388 p = 1) : d125660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d169388 q = 1) : d15607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55225 q ha hb
    | true =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55226 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d169388 q = 1) : d15608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d169388 q = 1) : d15609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d169388 q = 1) : d15610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d169388 q = 1) : d15617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55227 q ha hb
    | true =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55228 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d169388 q = 1) : d15618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d169388 q = 1) : d15619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d169388 q = 1) : d15647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55232 q ha hb
    | true =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55217 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d169388 q = 1) : d125656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d169388 q = 1) : d15704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55234 q ha hb
    | true =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d169388 q = 1) : d15705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d169388 q = 1) : d125657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d169388 q = 1) : d125658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d169388 q = 1) : d125659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128400 q = 1) (hb : d169388 q = 1) : d125660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128400, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128400, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55236 (p : Pattern) (ha : d17312 p = 1) (hb : d169388 p = 1) : d15710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d169388 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55208 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d169388 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d169388 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d169388 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d169388 q = 1) : d15603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17312 q = 1) (hb : d169388 q = 1) : d15710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17312, d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17312, d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55237 (p : Pattern) (ha : d17313 p = 1) (hb : d169388 p = 1) : d15711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d169388 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d169388 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d169388 q = 1) : d15605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17313 q = 1) (hb : d169388 q = 1) : d15711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17313, d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17313, d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55238 (p : Pattern) (ha : d17318 p = 1) (hb : d169388 p = 1) : d15716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d169388 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55208 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d169388 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d169388 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d169388 q = 1) : d15611 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d169388 q = 1) : d15612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17318 q = 1) (hb : d169388 q = 1) : d15716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17318, d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17318, d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55239 (p : Pattern) (ha : d17319 p = 1) (hb : d169388 p = 1) : d15717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d169388 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d169388 q = 1) : d15614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d169388 q = 1) : d15615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17319 q = 1) (hb : d169388 q = 1) : d15717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17319, d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17319, d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55240 (p : Pattern) (ha : d17323 p = 1) (hb : d169388 p = 1) : d15721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d169388 q = 1) : d15632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55231 q ha hb
    | true =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d169388 q = 1) : d15633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d169388 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55216 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d169388 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d169388 q = 1) : d15639 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d169388 q = 1) : d15640 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d169388 q = 1) : d15641 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17323 q = 1) (hb : d169388 q = 1) : d15721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17323, d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17323, d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55241 (p : Pattern) (ha : d17324 p = 1) (hb : d169388 p = 1) : d15722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d169388 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55216 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d169388 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d169388 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55209 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d169388 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d169388 q = 1) : d15643 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d169388 q = 1) : d15644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d169388 q = 1) : d15645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17324 q = 1) (hb : d169388 q = 1) : d15722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17324, d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17324, d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55242 (p : Pattern) (ha : d17330 p = 1) (hb : d169388 p = 1) : d15728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d169388 q = 1) : d15698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55233 q ha hb
    | true =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d169388 q = 1) : d15699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d169388 q = 1) : d15700 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d169388 q = 1) : d15701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d169388 q = 1) : d15702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17330 q = 1) (hb : d169388 q = 1) : d15728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17330, d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17330, d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55243 (p : Pattern) (ha : d128405 p = 1) (hb : d169388 p = 1) : d125665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d169388 q = 1) : d15607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55225 q ha hb
    | true =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55226 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d169388 q = 1) : d15608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d169388 q = 1) : d15609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d169388 q = 1) : d15610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d169388 q = 1) : d15617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55227 q ha hb
    | true =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55228 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d169388 q = 1) : d15618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d169388 q = 1) : d15619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d169388 q = 1) : d15647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55232 q ha hb
    | true =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55217 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d169388 q = 1) : d125656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d169388 q = 1) : d15704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55234 q ha hb
    | true =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d169388 q = 1) : d15705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d169388 q = 1) : d125657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d169388 q = 1) : d125658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d169388 q = 1) : d125659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17314 q = 1) (hb : d169388 q = 1) : d15712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17314, d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55236 q ha hb
    | true =>
      simp only [d17314, d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55237 q ha hb
  have h16 (q : Pattern) (ha : d17315 q = 1) (hb : d169388 q = 1) : d15713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17315, d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17315, d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17316 q = 1) (hb : d169388 q = 1) : d15714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17316, d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17316, d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d17317 q = 1) (hb : d169388 q = 1) : d15715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17317, d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17317, d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17320 q = 1) (hb : d169388 q = 1) : d15718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17320, d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55238 q ha hb
    | true =>
      simp only [d17320, d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55239 q ha hb
  have h20 (q : Pattern) (ha : d17321 q = 1) (hb : d169388 q = 1) : d15719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17321, d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17321, d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17322 q = 1) (hb : d169388 q = 1) : d15720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17322, d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17322, d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d17325 q = 1) (hb : d169388 q = 1) : d15723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55240 q ha hb
    | true =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55241 q ha hb
  have h23 (q : Pattern) (ha : d128401 q = 1) (hb : d169388 q = 1) : d125661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d17331 q = 1) (hb : d169388 q = 1) : d15729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55242 q ha hb
    | true =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d17332 q = 1) (hb : d169388 q = 1) : d15730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128402 q = 1) (hb : d169388 q = 1) : d125662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128403 q = 1) (hb : d169388 q = 1) : d125663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128403, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128403, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128404 q = 1) (hb : d169388 q = 1) : d125664 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128404, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128404, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128405 q = 1) (hb : d169388 q = 1) : d125665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128405, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128405, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro55244 (p : Pattern) (ha : d128412 p = 1) (hb : d169388 p = 1) : d125672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17325 q = 1) (hb : d169388 q = 1) : d15723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55240 q ha hb
    | true =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55241 q ha hb
  have h2 (q : Pattern) (ha : d128401 q = 1) (hb : d169388 q = 1) : d125661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17331 q = 1) (hb : d169388 q = 1) : d15729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55242 q ha hb
    | true =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17332 q = 1) (hb : d169388 q = 1) : d15730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128402 q = 1) (hb : d169388 q = 1) : d125662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128410 q = 1) (hb : d169388 q = 1) : d125670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128410, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128410, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128411 q = 1) (hb : d169388 q = 1) : d125671 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128411, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128411, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d169388 q = 1) : d125672 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55245 (p : Pattern) (ha : d17375 p = 1) (hb : d169388 p = 1) : d15768 p = 1 := by
  have h0 (q : Pattern) (ha : d2334 q = 1) (hb : d128484 q = 1) : d2334 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17373 q = 1) (hb : d169388 q = 1) : d15767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d169388, d15767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17373, d169388, d15767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128484 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17374 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d169388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17374, d169388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17375 q = 1) (hb : d169388 q = 1) : d15768 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17375, d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55246 (p : Pattern) (ha : d17382 p = 1) (hb : d169388 p = 1) : d15771 p = 1 := by
  have h0 (q : Pattern) (ha : d2338 q = 1) (hb : d128484 q = 1) : d2338 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17379 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17380 q = 1) (hb : d169388 q = 1) : d15769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d169388, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17380, d169388, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13816 q = 1) (hb : d128484 q = 1) : d13816 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15778 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17381 q = 1) (hb : d169388 q = 1) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d169388, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17381, d169388, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17382 q = 1) (hb : d169388 q = 1) : d15771 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d15771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17382, d15771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55247 (p : Pattern) (ha : d17386 p = 1) (hb : d169388 p = 1) : d15780 p = 1 := by
  have h0 (q : Pattern) (ha : d13816 q = 1) (hb : d128484 q = 1) : d13816 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17381 q = 1) (hb : d169388 q = 1) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d169388, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17381, d169388, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15779 q = 1) (hb : d169388 q = 1) : d15779 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17386 q = 1) (hb : d169388 q = 1) : d15780 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17386, d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro55248 (p : Pattern) (ha : d17405 p = 1) (hb : d169388 p = 1) : d15801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d169388 q = 1) : d15772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55245 q ha hb
    | true =>
      simp only [d17383, d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55246 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d169388 q = 1) : d15773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d169388 q = 1) : d15774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d169388 q = 1) : d15781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55246 q ha hb
    | true =>
      simp only [d17387, d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55247 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d169388 q = 1) : d15782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d169388 q = 1) : d15783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d169388 q = 1) : d15784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d169388 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55246 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55221 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d169388 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d169388 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15795 q = 1) (hb : d169388 q = 1) : d15795 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17400 q = 1) (hb : d169388 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55221 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17401 q = 1) (hb : d169388 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17402 q = 1) (hb : d169388 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17403 q = 1) (hb : d169388 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17404 q = 1) (hb : d169388 q = 1) : d15800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17405 q = 1) (hb : d169388 q = 1) : d15801 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17405, d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17405, d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro55249 (p : Pattern) (ha : d17410 p = 1) (hb : d169388 p = 1) : d15806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d169388 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55246 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55221 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d169388 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d169388 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d169388 q = 1) : d15795 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17400 q = 1) (hb : d169388 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55221 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d169388 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d169388 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d169388 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17408 q = 1) (hb : d169388 q = 1) : d15804 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17408, d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17409 q = 1) (hb : d169388 q = 1) : d15805 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17409, d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17410 q = 1) (hb : d169388 q = 1) : d15806 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17410, d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17410, d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
end NetHack.Soko22Hazard87
