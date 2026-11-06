import NetHack.Soko22Hazard87.AndIntroBlocks0413
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro103500 (p : Pattern) (ha : d242999 p = 1) (hb : d309132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242960 q = 1) (hb : d309101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242960, d309101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103496 q ha hb
    | true =>
      simp only [d242960, d309101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d242961 q = 1) (hb : d309102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242961, d309102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242961, d309102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d242962 q = 1) (hb : d309103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d242962, d309103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242962, d309103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242963 q = 1) (hb : d309104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d242963, d309104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242963, d309104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d242974 q = 1) (hb : d309113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242974, d309113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103497 q ha hb
    | true =>
      simp only [d242974, d309113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d242975 q = 1) (hb : d309114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242975, d309114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242975, d309114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d242976 q = 1) (hb : d309115 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d242976, d309115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242976, d309115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242977 q = 1) (hb : d309116 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d242977, d309116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242977, d309116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d242978 q = 1) (hb : d309117 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d242978, d309117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242978, d309117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242985 q = 1) (hb : d309119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103498 q ha hb
    | true =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d242986 q = 1) (hb : d309120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d242987 q = 1) (hb : d309121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d242987, d309121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242987, d309121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242988 q = 1) (hb : d309122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d242988, d309122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242988, d309122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d242994 q = 1) (hb : d309127 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
    | true =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d242995 q = 1) (hb : d309128 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d242996 q = 1) (hb : d309129 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d242996, d309129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242996, d309129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242997 q = 1) (hb : d309130 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d242997, d309130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242997, d309130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d242998 q = 1) (hb : d309131 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d242998, d309131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242998, d309131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d242999 q = 1) (hb : d309132 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d242999, d309132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242999, d309132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103501 (p : Pattern) (ha : d243006 p = 1) (hb : d309139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242380 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242954 q = 1) (hb : d309095 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242954, d309095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242954, d309095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242955 q = 1) (hb : d309096 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242955, d309096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242955, d309096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d242956 q = 1) (hb : d309097 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d242956, d309097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242956, d309097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236725 q = 1) (hb : d308523 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d236725, d308523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103395 q hb ha
    | true =>
      simp only [d236725, d308523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d236726 q = 1) (hb : d308524 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d236726, d308524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236726, d308524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d199013 q = 1) (hb : d308526 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d199014 q = 1) (hb : d308527 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d242382 q = 1) (hb : d308528 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d242382, d308528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242382, d308528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242964 q = 1) (hb : d309105 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d242964, d309105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242964, d309105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d242965 q = 1) (hb : d309106 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d242965, d309106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242965, d309106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d242967 q = 1) (hb : d309107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h13 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h14 (q : Pattern) (ha : d242969 q = 1) (hb : d309108 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d243000 q = 1) (hb : d309133 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d243000, d309133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d243000, d309133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q hb ha
  have h16 (q : Pattern) (ha : d243001 q = 1) (hb : d309134 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d243001, d309134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243001, d309134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h17 (q : Pattern) (ha : d243002 q = 1) (hb : d309135 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d243002, d309135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243002, d309135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d243003 q = 1) (hb : d309136 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d243003, d309136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243003, d309136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d243004 q = 1) (hb : d309137 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d243004, d309137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243004, d309137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d243005 q = 1) (hb : d309138 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d243005, d309138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d243005, d309138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h23 (q : Pattern) (ha : d243006 q = 1) (hb : d309139 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d243006, d309139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243006, d309139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro103502 (p : Pattern) (ha : d243011 p = 1) (hb : d309144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242967 q = 1) (hb : d309107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d242969 q = 1) (hb : d309108 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d243000 q = 1) (hb : d309133 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d243000, d309133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d243000, d309133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q hb ha
  have h5 (q : Pattern) (ha : d243001 q = 1) (hb : d309134 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d243001, d309134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243001, d309134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d243002 q = 1) (hb : d309135 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d243002, d309135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243002, d309135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199013 q = 1) (hb : d308526 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d199014 q = 1) (hb : d308527 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d243003 q = 1) (hb : d309136 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d243003, d309136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243003, d309136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d243004 q = 1) (hb : d309137 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d243004, d309137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243004, d309137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243005 q = 1) (hb : d309138 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d243005, d309138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243005, d309138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h15 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h16 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1577 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h18 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d32178 q = 1) (hb : d242991 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d32178, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d32179 q = 1) (hb : d242992 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d32179, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d243011 q = 1) (hb : d309144 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d243011, d309144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243011, d309144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  exact h24 p ha hb
theorem andIntro103503 (p : Pattern) (ha : d243018 p = 1) (hb : d309151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243007 q = 1) (hb : d309140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103501 q ha hb
    | true =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243008 q = 1) (hb : d309141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243009 q = 1) (hb : d309142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243009, d309142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243009, d309142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243010 q = 1) (hb : d309143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243010, d309143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243010, d309143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243012 q = 1) (hb : d309145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
    | true =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243013 q = 1) (hb : d309146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243014 q = 1) (hb : d309147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243014, d309147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243014, d309147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243015 q = 1) (hb : d309148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243015, d309148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243015, d309148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243016 q = 1) (hb : d309149 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243016, d309149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243016, d309149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242994 q = 1) (hb : d309127 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
    | true =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d242995 q = 1) (hb : d309128 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d242996 q = 1) (hb : d309129 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d242996, d309129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242996, d309129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242997 q = 1) (hb : d309130 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d242997, d309130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242997, d309130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d243017 q = 1) (hb : d309150 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243017, d309150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243017, d309150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d243018 q = 1) (hb : d309151 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243018, d309151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243018, d309151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103504 (p : Pattern) (ha : d243023 p = 1) (hb : d309156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243012 q = 1) (hb : d309145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
    | true =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243013 q = 1) (hb : d309146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243014 q = 1) (hb : d309147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243014, d309147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243014, d309147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243015 q = 1) (hb : d309148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243015, d309148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243015, d309148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243022 q = 1) (hb : d309155 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243022, d309155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243022, d309155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d243023 q = 1) (hb : d309156 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243023, d309156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243023, d309156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro103505 (p : Pattern) (ha : d243030 p = 1) (hb : d309163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243019 q = 1) (hb : d309152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243019, d309152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103500 q ha hb
    | true =>
      simp only [d243019, d309152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103503 q ha hb
  have h2 (q : Pattern) (ha : d243020 q = 1) (hb : d309153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243020, d309153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243020, d309153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243021 q = 1) (hb : d309154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243021, d309154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243021, d309154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243024 q = 1) (hb : d309157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103503 q ha hb
    | true =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103504 q ha hb
  have h5 (q : Pattern) (ha : d243025 q = 1) (hb : d309158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243026 q = 1) (hb : d309159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243027 q = 1) (hb : d309160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243027, d309160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243027, d309160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243028 q = 1) (hb : d309161 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243028, d309161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243028, d309161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243029 q = 1) (hb : d309162 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243029, d309162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243029, d309162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243030 q = 1) (hb : d309163 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243030, d309163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243030, d309163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro103506 (p : Pattern) (ha : d243034 p = 1) (hb : d309167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243024 q = 1) (hb : d309157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103503 q ha hb
    | true =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103504 q ha hb
  have h2 (q : Pattern) (ha : d243025 q = 1) (hb : d309158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243026 q = 1) (hb : d309159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243028 q = 1) (hb : d309161 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243028, d309161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243028, d309161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243033 q = 1) (hb : d309166 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243033, d309166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243033, d309166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243034 q = 1) (hb : d309167 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243034, d309167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243034, d309167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103507 (p : Pattern) (ha : d243040 p = 1) (hb : d309173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243037 q = 1) (hb : d309170 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243038 q = 1) (hb : d309171 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243039 q = 1) (hb : d309172 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243039, d309172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243039, d309172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243040 q = 1) (hb : d309173 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243040, d309173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243040, d309173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103508 (p : Pattern) (ha : d243044 p = 1) (hb : d309177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243041 q = 1) (hb : d309174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243042 q = 1) (hb : d309175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243043 q = 1) (hb : d309176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243043, d309176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243043, d309176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243044 q = 1) (hb : d309177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243044, d309177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243044, d309177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103509 (p : Pattern) (ha : d243050 p = 1) (hb : d309183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243045 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103507 q ha hb
    | true =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103508 q ha hb
  have h2 (q : Pattern) (ha : d243046 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243046, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243046, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243047 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243047, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243047, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243048 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243048, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243048, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243049 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243049, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243049, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243050 q = 1) (hb : d309183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243050, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243050, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103510 (p : Pattern) (ha : d243053 p = 1) (hb : d309186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243037 q = 1) (hb : d309170 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243038 q = 1) (hb : d309171 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243039 q = 1) (hb : d309172 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243039, d309172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243039, d309172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243053 q = 1) (hb : d309186 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243053, d309186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243053, d309186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro103511 (p : Pattern) (ha : d243054 p = 1) (hb : d309187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243041 q = 1) (hb : d309174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243042 q = 1) (hb : d309175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243043 q = 1) (hb : d309176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243043, d309176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243043, d309176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243054 q = 1) (hb : d309187 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243054, d309187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243054, d309187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103512 (p : Pattern) (ha : d243060 p = 1) (hb : d309193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243045 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103507 q ha hb
    | true =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103508 q ha hb
  have h2 (q : Pattern) (ha : d243046 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243046, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243046, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243047 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243047, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243047, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243048 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243048, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243048, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243049 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243049, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243049, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243055 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103510 q ha hb
    | true =>
      simp only [d243055, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103511 q ha hb
  have h7 (q : Pattern) (ha : d243056 q = 1) (hb : d309189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243056, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243056, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243057 q = 1) (hb : d309190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243057, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243057, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243058 q = 1) (hb : d309191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243058, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243058, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243059 q = 1) (hb : d309192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243059, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243059, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243060 q = 1) (hb : d309193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243060, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243060, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103513 (p : Pattern) (ha : d243065 p = 1) (hb : d309198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243037 q = 1) (hb : d309170 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243038 q = 1) (hb : d309171 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243064 q = 1) (hb : d309197 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243064, d309197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243064, d309197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243065 q = 1) (hb : d309198 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243065, d309198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243065, d309198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103514 (p : Pattern) (ha : d243067 p = 1) (hb : d309200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243041 q = 1) (hb : d309174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243042 q = 1) (hb : d309175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243066 q = 1) (hb : d309199 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243066, d309199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243066, d309199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243067 q = 1) (hb : d309200 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243067, d309200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243067, d309200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103515 (p : Pattern) (ha : d243074 p = 1) (hb : d309207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243037 q = 1) (hb : d309170 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243072 q = 1) (hb : d309205 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243072, d309205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243072, d309205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243073 q = 1) (hb : d309206 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243073, d309206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243073, d309206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243074 q = 1) (hb : d309207 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243074, d309207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243074, d309207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103516 (p : Pattern) (ha : d243077 p = 1) (hb : d309210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243041 q = 1) (hb : d309174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243075 q = 1) (hb : d309208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243075, d309208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243075, d309208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243076 q = 1) (hb : d309209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243076, d309209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243076, d309209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243077 q = 1) (hb : d309210 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243077, d309210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243077, d309210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103517 (p : Pattern) (ha : d243086 p = 1) (hb : d309214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242700 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242380 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242979 q = 1) (hb : d308265 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242979, d308265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242979, d308265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d242980 q = 1) (hb : d308266 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242980, d308266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242980, d308266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d242981 q = 1) (hb : d308522 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d242981, d308522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242981, d308522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242982 q = 1) (hb : d308858 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d242982, d308858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242982, d308858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d242983 q = 1) (hb : d308859 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d242983, d308859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242983, d308859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d243086 q = 1) (hb : d309214 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d243086, d309214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243086, d309214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103518 (p : Pattern) (ha : d243093 p = 1) (hb : d309221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243087 q = 1) (hb : d309215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243087, d309215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103517 q ha hb
    | true =>
      simp only [d243087, d309215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d243088 q = 1) (hb : d309216 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243088, d309216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243088, d309216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d243089 q = 1) (hb : d309217 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243089, d309217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243089, d309217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243090 q = 1) (hb : d309218 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243090, d309218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243090, d309218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d243091 q = 1) (hb : d309219 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243091, d309219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243091, d309219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242985 q = 1) (hb : d309119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103498 q ha hb
    | true =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d242986 q = 1) (hb : d309120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d242987 q = 1) (hb : d309121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d242987, d309121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242987, d309121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242988 q = 1) (hb : d309122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d242988, d309122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242988, d309122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d243092 q = 1) (hb : d309220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243092, d309220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243092, d309220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243093 q = 1) (hb : d309221 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243093, d309221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243093, d309221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro103519 (p : Pattern) (ha : d243099 p = 1) (hb : d309227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242380 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242954 q = 1) (hb : d309095 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242954, d309095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242954, d309095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242955 q = 1) (hb : d309096 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242955, d309096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242955, d309096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d242956 q = 1) (hb : d309097 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d242956, d309097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242956, d309097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243097 q = 1) (hb : d309225 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d243097, d309225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243097, d309225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d243098 q = 1) (hb : d309226 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d243098, d309226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243098, d309226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d242967 q = 1) (hb : d309107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h8 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h9 (q : Pattern) (ha : d242969 q = 1) (hb : d309108 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199013 q = 1) (hb : d308526 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d199014 q = 1) (hb : d308527 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d242970 q = 1) (hb : d309109 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d242970, d309109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242970, d309109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242971 q = 1) (hb : d309110 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d242971, d309110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242971, d309110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d242972 q = 1) (hb : d309111 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d242972, d309111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242972, d309111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d243099 q = 1) (hb : d309227 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d243099, d309227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243099, d309227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103520 (p : Pattern) (ha : d243105 p = 1) (hb : d309233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243100 q = 1) (hb : d309228 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243100, d309228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103519 q ha hb
    | true =>
      simp only [d243100, d309228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243101 q = 1) (hb : d309229 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243101, d309229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243101, d309229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243102 q = 1) (hb : d309230 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243102, d309230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243102, d309230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243103 q = 1) (hb : d309231 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243103, d309231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243103, d309231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d242994 q = 1) (hb : d309127 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
    | true =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d242995 q = 1) (hb : d309128 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d242996 q = 1) (hb : d309129 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d242996, d309129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242996, d309129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242997 q = 1) (hb : d309130 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d242997, d309130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242997, d309130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243104 q = 1) (hb : d309232 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243104, d309232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243104, d309232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243017 q = 1) (hb : d309150 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243017, d309150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243017, d309150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243105 q = 1) (hb : d309233 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243105, d309233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243105, d309233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103521 (p : Pattern) (ha : d243111 p = 1) (hb : d309239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243094 q = 1) (hb : d309222 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243094, d309222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103518 q ha hb
    | true =>
      simp only [d243094, d309222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103500 q ha hb
  have h2 (q : Pattern) (ha : d243095 q = 1) (hb : d309223 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243095, d309223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243095, d309223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243096 q = 1) (hb : d309224 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243096, d309224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243096, d309224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243106 q = 1) (hb : d309234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243106, d309234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103500 q ha hb
    | true =>
      simp only [d243106, d309234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103520 q ha hb
  have h5 (q : Pattern) (ha : d243107 q = 1) (hb : d309235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243107, d309235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243107, d309235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243108 q = 1) (hb : d309236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243108, d309236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243108, d309236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243109 q = 1) (hb : d309237 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243109, d309237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243109, d309237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243019 q = 1) (hb : d309152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243019, d309152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103500 q ha hb
    | true =>
      simp only [d243019, d309152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103503 q ha hb
  have h9 (q : Pattern) (ha : d243020 q = 1) (hb : d309153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243020, d309153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243020, d309153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243021 q = 1) (hb : d309154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243021, d309154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243021, d309154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243024 q = 1) (hb : d309157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103503 q ha hb
    | true =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103504 q ha hb
  have h12 (q : Pattern) (ha : d243025 q = 1) (hb : d309158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243026 q = 1) (hb : d309159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243027 q = 1) (hb : d309160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243027, d309160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243027, d309160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243110 q = 1) (hb : d309238 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243110, d309238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243110, d309238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243111 q = 1) (hb : d309239 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243111, d309239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243111, d309239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro103522 (p : Pattern) (ha : d243117 p = 1) (hb : d309245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243112 q = 1) (hb : d309240 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243112, d309240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103521 q ha hb
    | true =>
      simp only [d243112, d309240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243113 q = 1) (hb : d309241 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243113, d309241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243113, d309241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243114 q = 1) (hb : d309242 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243114, d309242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243114, d309242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243115 q = 1) (hb : d309243 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243115, d309243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243115, d309243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243116 q = 1) (hb : d309244 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243116, d309244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243116, d309244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243117 q = 1) (hb : d309245 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243117, d309245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243117, d309245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103523 (p : Pattern) (ha : d243120 p = 1) (hb : d309248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242967 q = 1) (hb : d309107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d242969 q = 1) (hb : d309108 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d199013 q = 1) (hb : d308526 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d199014 q = 1) (hb : d308527 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d242970 q = 1) (hb : d309109 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d242970, d309109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242970, d309109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199015 q = 1) (hb : d309123 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d199015, d309123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199015, d309123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d242989 q = 1) (hb : d309124 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d242989, d309124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242989, d309124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242990 q = 1) (hb : d309125 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d242990, d309125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242990, d309125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h11 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d243120 q = 1) (hb : d309248 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d243120, d309248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243120, d309248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  exact h18 p ha hb
theorem andIntro103524 (p : Pattern) (ha : d243126 p = 1) (hb : d309254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243007 q = 1) (hb : d309140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103501 q ha hb
    | true =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243008 q = 1) (hb : d309141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243009 q = 1) (hb : d309142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243009, d309142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243009, d309142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243010 q = 1) (hb : d309143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243010, d309143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243010, d309143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243012 q = 1) (hb : d309145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
    | true =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243013 q = 1) (hb : d309146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243014 q = 1) (hb : d309147 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243014, d309147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243014, d309147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243015 q = 1) (hb : d309148 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243015, d309148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243015, d309148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243016 q = 1) (hb : d309149 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243016, d309149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243016, d309149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243121 q = 1) (hb : d309249 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243121, d309249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103523 q ha hb
    | true =>
      simp only [d243121, d309249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243122 q = 1) (hb : d309250 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243122, d309250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243122, d309250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d243123 q = 1) (hb : d309251 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243123, d309251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243123, d309251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243124 q = 1) (hb : d309252 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243124, d309252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243124, d309252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d243125 q = 1) (hb : d309253 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243125, d309253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243125, d309253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d243126 q = 1) (hb : d309254 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243126, d309254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243126, d309254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103525 (p : Pattern) (ha : d243127 p = 1) (hb : d309255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242967 q = 1) (hb : d309107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103495 q ha hb
    | true =>
      simp only [d242967, d309107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d242969 q = 1) (hb : d309108 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242969, d309108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d243000 q = 1) (hb : d309133 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d243000, d309133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d243000, d309133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q hb ha
  have h5 (q : Pattern) (ha : d243001 q = 1) (hb : d309134 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d243001, d309134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243001, d309134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d243002 q = 1) (hb : d309135 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d243002, d309135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243002, d309135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199013 q = 1) (hb : d308526 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103396 q ha hb
    | true =>
      simp only [d199013, d308526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d199014 q = 1) (hb : d308527 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199014, d308527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d243003 q = 1) (hb : d309136 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d243003, d309136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243003, d309136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d243004 q = 1) (hb : d309137 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d243004, d309137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243004, d309137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243005 q = 1) (hb : d309138 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d243005, d309138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243005, d309138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h15 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d243127 q = 1) (hb : d309255 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d243127, d309255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243127, d309255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro103526 (p : Pattern) (ha : d243133 p = 1) (hb : d309261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243128 q = 1) (hb : d309256 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243128, d309256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103525 q ha hb
    | true =>
      simp only [d243128, d309256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243129 q = 1) (hb : d309257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243129, d309257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243129, d309257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243130 q = 1) (hb : d309258 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243130, d309258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243130, d309258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243131 q = 1) (hb : d309259 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243131, d309259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243131, d309259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243132 q = 1) (hb : d309260 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243132, d309260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243132, d309260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243133 q = 1) (hb : d309261 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243133, d309261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243133, d309261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103527 (p : Pattern) (ha : d243139 p = 1) (hb : d309267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243019 q = 1) (hb : d309152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243019, d309152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103500 q ha hb
    | true =>
      simp only [d243019, d309152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103503 q ha hb
  have h2 (q : Pattern) (ha : d243020 q = 1) (hb : d309153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243020, d309153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243020, d309153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243021 q = 1) (hb : d309154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243021, d309154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243021, d309154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243024 q = 1) (hb : d309157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103503 q ha hb
    | true =>
      simp only [d243024, d309157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103504 q ha hb
  have h5 (q : Pattern) (ha : d243025 q = 1) (hb : d309158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243025, d309158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243026 q = 1) (hb : d309159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243026, d309159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243027 q = 1) (hb : d309160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243027, d309160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243027, d309160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243134 q = 1) (hb : d309262 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243134, d309262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103524 q ha hb
    | true =>
      simp only [d243134, d309262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103526 q ha hb
  have h9 (q : Pattern) (ha : d243135 q = 1) (hb : d309263 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243135, d309263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243135, d309263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243136 q = 1) (hb : d309264 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243136, d309264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243136, d309264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243137 q = 1) (hb : d309265 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243137, d309265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243137, d309265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d243138 q = 1) (hb : d309266 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243138, d309266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243138, d309266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243139 q = 1) (hb : d309267 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243139, d309267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243139, d309267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro103528 (p : Pattern) (ha : d243145 p = 1) (hb : d309273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243140 q = 1) (hb : d309268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243140, d309268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103527 q ha hb
    | true =>
      simp only [d243140, d309268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243141 q = 1) (hb : d309269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243141, d309269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243141, d309269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243142 q = 1) (hb : d309270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243142, d309270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243142, d309270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243143 q = 1) (hb : d309271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243143, d309271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243143, d309271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243144 q = 1) (hb : d309272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243144, d309272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243144, d309272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243145 q = 1) (hb : d309273 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243145, d309273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243145, d309273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103529 (p : Pattern) (ha : d243151 p = 1) (hb : d309279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243068 q = 1) (hb : d309201 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243068, d309201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103513 q ha hb
    | true =>
      simp only [d243068, d309201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103514 q ha hb
  have h2 (q : Pattern) (ha : d243069 q = 1) (hb : d309202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243069, d309202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243069, d309202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243070 q = 1) (hb : d309203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243070, d309203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243070, d309203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243071 q = 1) (hb : d309204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243071, d309204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243071, d309204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243078 q = 1) (hb : d309211 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243078, d309211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103515 q ha hb
    | true =>
      simp only [d243078, d309211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103516 q ha hb
  have h6 (q : Pattern) (ha : d243079 q = 1) (hb : d309212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243079, d309212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243079, d309212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243080 q = 1) (hb : d309213 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243080, d309213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243080, d309213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243118 q = 1) (hb : d309246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243118, d309246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103522 q ha hb
    | true =>
      simp only [d243118, d309246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103507 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243045 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d243119 q = 1) (hb : d309247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d309247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243119, d309247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d243146 q = 1) (hb : d309274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243146, d309274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103528 q ha hb
    | true =>
      simp only [d243146, d309274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d243147 q = 1) (hb : d309275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243147, d309275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243147, d309275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243148 q = 1) (hb : d309276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d309276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243148, d309276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243149 q = 1) (hb : d309277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d309277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243149, d309277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243150 q = 1) (hb : d309278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d309278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243150, d309278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243151 q = 1) (hb : d309279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243151, d309279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243151, d309279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro103530 (p : Pattern) (ha : d243152 p = 1) (hb : d309280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243037 q = 1) (hb : d309170 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243038 q = 1) (hb : d309171 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243038, d309171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243064 q = 1) (hb : d309197 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243064, d309197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243064, d309197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243152 q = 1) (hb : d309280 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243152, d309280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243152, d309280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro103531 (p : Pattern) (ha : d243153 p = 1) (hb : d309281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243041 q = 1) (hb : d309174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243042 q = 1) (hb : d309175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243042, d309175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243066 q = 1) (hb : d309199 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243066, d309199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243066, d309199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243153 q = 1) (hb : d309281 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243153, d309281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243153, d309281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103532 (p : Pattern) (ha : d243158 p = 1) (hb : d309286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243037 q = 1) (hb : d309170 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243037, d309170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243072 q = 1) (hb : d309205 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243072, d309205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243072, d309205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243073 q = 1) (hb : d309206 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243073, d309206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243073, d309206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243158 q = 1) (hb : d309286 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243158, d309286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243158, d309286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro103533 (p : Pattern) (ha : d243159 p = 1) (hb : d309287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243035 q = 1) (hb : d309168 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103506 q ha hb
    | true =>
      simp only [d243035, d309168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243036 q = 1) (hb : d309169 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243036, d309169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243041 q = 1) (hb : d309174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243041, d309174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243075 q = 1) (hb : d309208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243075, d309208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243075, d309208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243076 q = 1) (hb : d309209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243076, d309209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243076, d309209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243159 q = 1) (hb : d309287 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243159, d309287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243159, d309287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103534 (p : Pattern) (ha : d243163 p = 1) (hb : d309291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243112 q = 1) (hb : d309240 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243112, d309240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103521 q ha hb
    | true =>
      simp only [d243112, d309240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243113 q = 1) (hb : d309241 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243113, d309241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243113, d309241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243031 q = 1) (hb : d309164 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103505 q ha hb
    | true =>
      simp only [d243031, d309164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243032 q = 1) (hb : d309165 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243032, d309165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243114 q = 1) (hb : d309242 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243114, d309242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243114, d309242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243115 q = 1) (hb : d309243 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243115, d309243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243115, d309243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243116 q = 1) (hb : d309244 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243116, d309244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243116, d309244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243163 q = 1) (hb : d309291 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243163, d309291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243163, d309291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro103535 (p : Pattern) (ha : d243166 p = 1) (hb : d309294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243140 q = 1) (hb : d309268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243140, d309268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103527 q ha hb
    | true =>
      simp only [d243140, d309268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243141 q = 1) (hb : d309269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243141, d309269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243141, d309269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243142 q = 1) (hb : d309270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243142, d309270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243142, d309270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243143 q = 1) (hb : d309271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243143, d309271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243143, d309271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243144 q = 1) (hb : d309272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243144, d309272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243144, d309272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243166 q = 1) (hb : d309294 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243166, d309294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243166, d309294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103536 (p : Pattern) (ha : d243172 p = 1) (hb : d309300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243068 q = 1) (hb : d309201 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243068, d309201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103513 q ha hb
    | true =>
      simp only [d243068, d309201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103514 q ha hb
  have h2 (q : Pattern) (ha : d243069 q = 1) (hb : d309202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243069, d309202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243069, d309202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243070 q = 1) (hb : d309203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243070, d309203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243070, d309203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243071 q = 1) (hb : d309204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243071, d309204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243071, d309204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243078 q = 1) (hb : d309211 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243078, d309211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103515 q ha hb
    | true =>
      simp only [d243078, d309211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103516 q ha hb
  have h6 (q : Pattern) (ha : d243079 q = 1) (hb : d309212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243079, d309212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243079, d309212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243080 q = 1) (hb : d309213 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243080, d309213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243080, d309213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243118 q = 1) (hb : d309246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243118, d309246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103522 q ha hb
    | true =>
      simp only [d243118, d309246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103507 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243045 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d243119 q = 1) (hb : d309247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d309247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243119, d309247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d243146 q = 1) (hb : d309274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243146, d309274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103528 q ha hb
    | true =>
      simp only [d243146, d309274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d243147 q = 1) (hb : d309275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243147, d309275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243147, d309275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243148 q = 1) (hb : d309276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d309276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243148, d309276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243149 q = 1) (hb : d309277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d309277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243149, d309277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243150 q = 1) (hb : d309278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d309278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243150, d309278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243154 q = 1) (hb : d309282 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243154, d309282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103530 q ha hb
    | true =>
      simp only [d243154, d309282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103531 q ha hb
  have h17 (q : Pattern) (ha : d243155 q = 1) (hb : d309283 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243155, d309283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243155, d309283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243156 q = 1) (hb : d309284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243156, d309284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243156, d309284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d243157 q = 1) (hb : d309285 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243157, d309285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243157, d309285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d243160 q = 1) (hb : d309288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243160, d309288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103532 q ha hb
    | true =>
      simp only [d243160, d309288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103533 q ha hb
  have h21 (q : Pattern) (ha : d243161 q = 1) (hb : d309289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243161, d309289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243161, d309289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d243162 q = 1) (hb : d309290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243162, d309290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d243162, d309290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d243164 q = 1) (hb : d309292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243164, d309292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103534 q ha hb
    | true =>
      simp only [d243164, d309292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103510 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d243055 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d243165 q = 1) (hb : d309293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d309293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d243165, d309293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d243167 q = 1) (hb : d309295 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243167, d309295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103535 q ha hb
    | true =>
      simp only [d243167, d309295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d243168 q = 1) (hb : d309296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243168, d309296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d243168, d309296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d243169 q = 1) (hb : d309297 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d309297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d243169, d309297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d243170 q = 1) (hb : d309298 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243170, d309298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d243170, d309298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d243171 q = 1) (hb : d309299 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243171, d309299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243171, d309299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d243172 q = 1) (hb : d309300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243172, d309300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243172, d309300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro103537 (p : Pattern) (ha : d243179 p = 1) (hb : d309307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243045 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103507 q ha hb
    | true =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103508 q ha hb
  have h2 (q : Pattern) (ha : d243046 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243046, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243046, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243047 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243047, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243047, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243048 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243048, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243048, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243049 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243049, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243049, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243174 q = 1) (hb : d309302 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243174, d309302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103508 q ha hb
    | true =>
      simp only [d243174, d309302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243175 q = 1) (hb : d309303 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243175, d309303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243175, d309303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243176 q = 1) (hb : d309304 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243176, d309304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243176, d309304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243177 q = 1) (hb : d309305 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243177, d309305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243177, d309305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243178 q = 1) (hb : d309306 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243178, d309306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243178, d309306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243179 q = 1) (hb : d309307 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243179, d309307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243179, d309307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103538 (p : Pattern) (ha : d243185 p = 1) (hb : d309313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243174 q = 1) (hb : d309302 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243174, d309302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103508 q ha hb
    | true =>
      simp only [d243174, d309302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243175 q = 1) (hb : d309303 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243175, d309303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243175, d309303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243176 q = 1) (hb : d309304 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243176, d309304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243176, d309304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243177 q = 1) (hb : d309305 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243177, d309305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243177, d309305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243178 q = 1) (hb : d309306 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243178, d309306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243178, d309306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243180 q = 1) (hb : d309308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243180, d309308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103511 q ha hb
    | true =>
      simp only [d243180, d309308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243181 q = 1) (hb : d309309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243181, d309309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243181, d309309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243182 q = 1) (hb : d309310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243182, d309310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243182, d309310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243183 q = 1) (hb : d309311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243183, d309311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243183, d309311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243184 q = 1) (hb : d309312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243184, d309312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243184, d309312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243185 q = 1) (hb : d309313 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243185, d309313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243185, d309313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103539 (p : Pattern) (ha : d243192 p = 1) (hb : d309320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243164 q = 1) (hb : d309292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243164, d309292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103534 q ha hb
    | true =>
      simp only [d243164, d309292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103510 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243055 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243165 q = 1) (hb : d309293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d309293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243165, d309293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d243167 q = 1) (hb : d309295 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243167, d309295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103535 q ha hb
    | true =>
      simp only [d243167, d309295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243168 q = 1) (hb : d309296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243168, d309296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243168, d309296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243169 q = 1) (hb : d309297 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d309297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243169, d309297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243190 q = 1) (hb : d309318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243190, d309318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243190, d309318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243191 q = 1) (hb : d309319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243191, d309319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243191, d309319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243192 q = 1) (hb : d309320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243192, d309320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243192, d309320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro103540 (p : Pattern) (ha : d243194 p = 1) (hb : d309322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243180 q = 1) (hb : d309308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243180, d309308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103511 q ha hb
    | true =>
      simp only [d243180, d309308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243181 q = 1) (hb : d309309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243181, d309309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243181, d309309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243182 q = 1) (hb : d309310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243182, d309310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243182, d309310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243183 q = 1) (hb : d309311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243183, d309311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243183, d309311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243184 q = 1) (hb : d309312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243184, d309312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243184, d309312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243194 q = 1) (hb : d309322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243194, d309322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243194, d309322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103541 (p : Pattern) (ha : d243214 p = 1) (hb : d309338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243203 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243204 q = 1) (hb : d309328 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243204, d309328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243204, d309328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103517 q ha hb
  have h3 (q : Pattern) (ha : d243087 q = 1) (hb : d309215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243087, d309215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103517 q ha hb
    | true =>
      simp only [d243087, d309215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d243205 q = 1) (hb : d309329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243205, d309329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243205, d309329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243088 q = 1) (hb : d309216 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243088, d309216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243088, d309216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d243206 q = 1) (hb : d309330 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243206, d309330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243206, d309330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243207 q = 1) (hb : d309331 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243207, d309331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243207, d309331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d243208 q = 1) (hb : d309332 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243208, d309332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243208, d309332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243209 q = 1) (hb : d309333 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243209, d309333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243209, d309333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103498 q ha hb
  have h10 (q : Pattern) (ha : d242985 q = 1) (hb : d309119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103498 q ha hb
    | true =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d243210 q = 1) (hb : d309334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243210, d309334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243210, d309334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d242986 q = 1) (hb : d309120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d243211 q = 1) (hb : d309335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243211, d309335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243211, d309335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243212 q = 1) (hb : d309336 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243212, d309336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243212, d309336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d243213 q = 1) (hb : d309337 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243213, d309337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243213, d309337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243214 q = 1) (hb : d309338 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243214, d309338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243214, d309338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro103542 (p : Pattern) (ha : d243229 p = 1) (hb : d309353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243215 q = 1) (hb : d309339 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243215, d309339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243215, d309339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103496 q ha hb
  have h2 (q : Pattern) (ha : d242960 q = 1) (hb : d309101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242960, d309101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103496 q ha hb
    | true =>
      simp only [d242960, d309101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243216 q = 1) (hb : d309340 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243216, d309340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243216, d309340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242961 q = 1) (hb : d309102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242961, d309102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d242961, d309102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243217 q = 1) (hb : d309341 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243217, d309341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243217, d309341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243218 q = 1) (hb : d309342 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243218, d309342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243218, d309342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243219 q = 1) (hb : d309343 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243219, d309343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243219, d309343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103497 q ha hb
  have h8 (q : Pattern) (ha : d242974 q = 1) (hb : d309113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242974, d309113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103497 q ha hb
    | true =>
      simp only [d242974, d309113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243220 q = 1) (hb : d309344 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243220, d309344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243220, d309344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242975 q = 1) (hb : d309114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242975, d309114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242975, d309114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243221 q = 1) (hb : d309345 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243221, d309345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243221, d309345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243222 q = 1) (hb : d309346 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243222, d309346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243222, d309346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243223 q = 1) (hb : d309347 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243223, d309347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243223, d309347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243209 q = 1) (hb : d309333 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243209, d309333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243209, d309333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103498 q ha hb
  have h15 (q : Pattern) (ha : d242985 q = 1) (hb : d309119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103498 q ha hb
    | true =>
      simp only [d242985, d309119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243210 q = 1) (hb : d309334 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243210, d309334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243210, d309334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242986 q = 1) (hb : d309120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242986, d309120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d243211 q = 1) (hb : d309335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243211, d309335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243211, d309335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d243212 q = 1) (hb : d309336 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243212, d309336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d243212, d309336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d243224 q = 1) (hb : d309348 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243224, d309348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243224, d309348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
  have h21 (q : Pattern) (ha : d242994 q = 1) (hb : d309127 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
    | true =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d243225 q = 1) (hb : d309349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243225, d309349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d243225, d309349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d242995 q = 1) (hb : d309128 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d243226 q = 1) (hb : d309350 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243226, d309350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d243226, d309350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d243227 q = 1) (hb : d309351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243227, d309351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d243227, d309351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d243228 q = 1) (hb : d309352 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243228, d309352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243228, d309352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d243229 q = 1) (hb : d309353 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243229, d309353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243229, d309353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro103543 (p : Pattern) (ha : d243239 p = 1) (hb : d309363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243233 q = 1) (hb : d309357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243233, d309357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243233, d309357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103519 q ha hb
  have h2 (q : Pattern) (ha : d243100 q = 1) (hb : d309228 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243100, d309228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103519 q ha hb
    | true =>
      simp only [d243100, d309228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243234 q = 1) (hb : d309358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243234, d309358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243234, d309358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243101 q = 1) (hb : d309229 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243101, d309229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243101, d309229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243235 q = 1) (hb : d309359 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243235, d309359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243235, d309359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243236 q = 1) (hb : d309360 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243236, d309360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243236, d309360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243224 q = 1) (hb : d309348 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243224, d309348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243224, d309348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
  have h8 (q : Pattern) (ha : d242994 q = 1) (hb : d309127 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
    | true =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243225 q = 1) (hb : d309349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243225, d309349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243225, d309349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242995 q = 1) (hb : d309128 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243226 q = 1) (hb : d309350 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243226, d309350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243226, d309350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243227 q = 1) (hb : d309351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243227, d309351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243227, d309351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243237 q = 1) (hb : d309361 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243237, d309361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243237, d309361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243238 q = 1) (hb : d309362 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243238, d309362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243238, d309362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d243239 q = 1) (hb : d309363 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243239, d309363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243239, d309363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103544 (p : Pattern) (ha : d243253 p = 1) (hb : d309377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243244 q = 1) (hb : d309368 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243244, d309368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243244, d309368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103501 q ha hb
  have h2 (q : Pattern) (ha : d243007 q = 1) (hb : d309140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103501 q ha hb
    | true =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243245 q = 1) (hb : d309369 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243245, d309369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243245, d309369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243008 q = 1) (hb : d309141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243246 q = 1) (hb : d309370 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243246, d309370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243246, d309370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243247 q = 1) (hb : d309371 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243247, d309371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243247, d309371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243248 q = 1) (hb : d309372 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243248, d309372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243248, d309372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
  have h8 (q : Pattern) (ha : d243012 q = 1) (hb : d309145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
    | true =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243249 q = 1) (hb : d309373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243249, d309373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243249, d309373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243013 q = 1) (hb : d309146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243250 q = 1) (hb : d309374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243250, d309374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243250, d309374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243251 q = 1) (hb : d309375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243251, d309375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243251, d309375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243252 q = 1) (hb : d309376 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243252, d309376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243252, d309376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243224 q = 1) (hb : d309348 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243224, d309348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243224, d309348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
  have h15 (q : Pattern) (ha : d242994 q = 1) (hb : d309127 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103499 q ha hb
    | true =>
      simp only [d242994, d309127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243225 q = 1) (hb : d309349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243225, d309349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243225, d309349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242995 q = 1) (hb : d309128 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242995, d309128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d243226 q = 1) (hb : d309350 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243226, d309350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243226, d309350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d243227 q = 1) (hb : d309351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243227, d309351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d243227, d309351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d243238 q = 1) (hb : d309362 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243238, d309362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243238, d309362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d243253 q = 1) (hb : d309377 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243253, d309377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243253, d309377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro103545 (p : Pattern) (ha : d243258 p = 1) (hb : d309382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243248 q = 1) (hb : d309372 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243248, d309372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243248, d309372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
  have h2 (q : Pattern) (ha : d243012 q = 1) (hb : d309145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
    | true =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243249 q = 1) (hb : d309373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243249, d309373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243249, d309373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243013 q = 1) (hb : d309146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243250 q = 1) (hb : d309374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243250, d309374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243250, d309374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243251 q = 1) (hb : d309375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243251, d309375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243251, d309375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243257 q = 1) (hb : d309381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243257, d309381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243257, d309381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d243258 q = 1) (hb : d309382 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243258, d309382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243258, d309382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro103546 (p : Pattern) (ha : d243264 p = 1) (hb : d309388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243230 q = 1) (hb : d309354 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243230, d309354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103541 q ha hb
    | true =>
      simp only [d243230, d309354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103542 q ha hb
  have h2 (q : Pattern) (ha : d243231 q = 1) (hb : d309355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243231, d309355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243231, d309355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243232 q = 1) (hb : d309356 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243232, d309356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243232, d309356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243240 q = 1) (hb : d309364 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243240, d309364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103542 q ha hb
    | true =>
      simp only [d243240, d309364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103543 q ha hb
  have h5 (q : Pattern) (ha : d243241 q = 1) (hb : d309365 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243241, d309365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243241, d309365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243242 q = 1) (hb : d309366 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243242, d309366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243242, d309366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243243 q = 1) (hb : d309367 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243243, d309367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243243, d309367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243254 q = 1) (hb : d309378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243254, d309378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103542 q ha hb
    | true =>
      simp only [d243254, d309378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103544 q ha hb
  have h9 (q : Pattern) (ha : d243255 q = 1) (hb : d309379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243255, d309379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243255, d309379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243256 q = 1) (hb : d309380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243256, d309380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243256, d309380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243259 q = 1) (hb : d309383 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103544 q ha hb
    | true =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103545 q ha hb
  have h12 (q : Pattern) (ha : d243260 q = 1) (hb : d309384 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243261 q = 1) (hb : d309385 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243262 q = 1) (hb : d309386 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243262, d309386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243262, d309386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243263 q = 1) (hb : d309387 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243263, d309387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243263, d309387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243264 q = 1) (hb : d309388 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243264, d309388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243264, d309388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro103547 (p : Pattern) (ha : d243269 p = 1) (hb : d309393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243254 q = 1) (hb : d309378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243254, d309378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103542 q ha hb
    | true =>
      simp only [d243254, d309378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103544 q ha hb
  have h2 (q : Pattern) (ha : d243255 q = 1) (hb : d309379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243255, d309379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243255, d309379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243256 q = 1) (hb : d309380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243256, d309380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243256, d309380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243259 q = 1) (hb : d309383 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103544 q ha hb
    | true =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103545 q ha hb
  have h5 (q : Pattern) (ha : d243260 q = 1) (hb : d309384 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243261 q = 1) (hb : d309385 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243262 q = 1) (hb : d309386 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243262, d309386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243262, d309386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243267 q = 1) (hb : d309391 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243267, d309391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243267, d309391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243268 q = 1) (hb : d309392 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243268, d309392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243268, d309392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243269 q = 1) (hb : d309393 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243269, d309393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243269, d309393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro103548 (p : Pattern) (ha : d243275 p = 1) (hb : d309399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243265 q = 1) (hb : d309389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243265, d309389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103546 q ha hb
    | true =>
      simp only [d243265, d309389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243266 q = 1) (hb : d309390 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243266, d309390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243266, d309390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243270 q = 1) (hb : d309394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243270, d309394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103547 q ha hb
    | true =>
      simp only [d243270, d309394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243271 q = 1) (hb : d309395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243271, d309395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243271, d309395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243272 q = 1) (hb : d309396 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243272, d309396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243272, d309396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243273 q = 1) (hb : d309397 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243273, d309397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243273, d309397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243274 q = 1) (hb : d309398 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243274, d309398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243274, d309398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243275 q = 1) (hb : d309399 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243275, d309399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243275, d309399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro103549 (p : Pattern) (ha : d243277 p = 1) (hb : d309401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243259 q = 1) (hb : d309383 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103544 q ha hb
    | true =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103545 q ha hb
  have h2 (q : Pattern) (ha : d243260 q = 1) (hb : d309384 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243261 q = 1) (hb : d309385 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243267 q = 1) (hb : d309391 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243267, d309391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243267, d309391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243276 q = 1) (hb : d309400 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243276, d309400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243276, d309400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243277 q = 1) (hb : d309401 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243277, d309401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243277, d309401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103550 (p : Pattern) (ha : d243283 p = 1) (hb : d309407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243270 q = 1) (hb : d309394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243270, d309394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103547 q ha hb
    | true =>
      simp only [d243270, d309394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243271 q = 1) (hb : d309395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243271, d309395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243271, d309395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243278 q = 1) (hb : d309402 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243278, d309402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103549 q ha hb
    | true =>
      simp only [d243278, d309402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243279 q = 1) (hb : d309403 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243279, d309403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243279, d309403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243280 q = 1) (hb : d309404 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243280, d309404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243280, d309404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243281 q = 1) (hb : d309405 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243281, d309405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243281, d309405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243282 q = 1) (hb : d309406 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243282, d309406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243282, d309406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243283 q = 1) (hb : d309407 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243283, d309407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243283, d309407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro103551 (p : Pattern) (ha : d243296 p = 1) (hb : d309415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243244 q = 1) (hb : d309368 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243244, d309368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243244, d309368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103501 q ha hb
  have h2 (q : Pattern) (ha : d243007 q = 1) (hb : d309140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103501 q ha hb
    | true =>
      simp only [d243007, d309140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243245 q = 1) (hb : d309369 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243245, d309369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243245, d309369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243008 q = 1) (hb : d309141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243008, d309141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243246 q = 1) (hb : d309370 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243246, d309370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243246, d309370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243247 q = 1) (hb : d309371 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243247, d309371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243247, d309371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243248 q = 1) (hb : d309372 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243248, d309372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243248, d309372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
  have h8 (q : Pattern) (ha : d243012 q = 1) (hb : d309145 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103502 q ha hb
    | true =>
      simp only [d243012, d309145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d243249 q = 1) (hb : d309373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243249, d309373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243249, d309373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243013 q = 1) (hb : d309146 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243013, d309146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d243250 q = 1) (hb : d309374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243250, d309374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243250, d309374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d243251 q = 1) (hb : d309375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243251, d309375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243251, d309375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d243252 q = 1) (hb : d309376 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243252, d309376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243252, d309376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243291 q = 1) (hb : d309410 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243291, d309410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243291, d309410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103523 q ha hb
  have h15 (q : Pattern) (ha : d243121 q = 1) (hb : d309249 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243121, d309249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103523 q ha hb
    | true =>
      simp only [d243121, d309249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243292 q = 1) (hb : d309411 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243292, d309411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243292, d309411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243122 q = 1) (hb : d309250 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243122, d309250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243122, d309250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d243293 q = 1) (hb : d309412 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243293, d309412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243293, d309412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d243294 q = 1) (hb : d309413 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243294, d309413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d243294, d309413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d243295 q = 1) (hb : d309414 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243295, d309414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243295, d309414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d243296 q = 1) (hb : d309415 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243296, d309415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243296, d309415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro103552 (p : Pattern) (ha : d243302 p = 1) (hb : d309421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243297 q = 1) (hb : d309416 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243297, d309416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243297, d309416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103525 q ha hb
  have h2 (q : Pattern) (ha : d243128 q = 1) (hb : d309256 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d243128, d309256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103525 q ha hb
    | true =>
      simp only [d243128, d309256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243298 q = 1) (hb : d309417 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243298, d309417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243298, d309417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243129 q = 1) (hb : d309257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d243129, d309257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243129, d309257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243299 q = 1) (hb : d309418 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d243299, d309418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243299, d309418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243300 q = 1) (hb : d309419 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d243300, d309419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243300, d309419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d243301 q = 1) (hb : d309420 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d243301, d309420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243301, d309420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d243302 q = 1) (hb : d309421 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d243302, d309421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243302, d309421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro103553 (p : Pattern) (ha : d243308 p = 1) (hb : d309427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243254 q = 1) (hb : d309378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243254, d309378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103542 q ha hb
    | true =>
      simp only [d243254, d309378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103544 q ha hb
  have h2 (q : Pattern) (ha : d243255 q = 1) (hb : d309379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243255, d309379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243255, d309379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243256 q = 1) (hb : d309380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243256, d309380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243256, d309380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243259 q = 1) (hb : d309383 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103544 q ha hb
    | true =>
      simp only [d243259, d309383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103545 q ha hb
  have h5 (q : Pattern) (ha : d243260 q = 1) (hb : d309384 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243260, d309384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243261 q = 1) (hb : d309385 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243261, d309385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243262 q = 1) (hb : d309386 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243262, d309386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243262, d309386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243303 q = 1) (hb : d309422 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d243303, d309422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103551 q ha hb
    | true =>
      simp only [d243303, d309422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103552 q ha hb
  have h9 (q : Pattern) (ha : d243304 q = 1) (hb : d309423 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d243304, d309423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243304, d309423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243305 q = 1) (hb : d309424 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d243305, d309424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243305, d309424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243306 q = 1) (hb : d309425 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d243306, d309425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243306, d309425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d243307 q = 1) (hb : d309426 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d243307, d309426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243307, d309426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243308 q = 1) (hb : d309427 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d243308, d309427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243308, d309427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro103554 (p : Pattern) (ha : d243314 p = 1) (hb : d309433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243309 q = 1) (hb : d309428 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243309, d309428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103553 q ha hb
    | true =>
      simp only [d243309, d309428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243310 q = 1) (hb : d309429 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243310, d309429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243310, d309429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243311 q = 1) (hb : d309430 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243311, d309430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243311, d309430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243312 q = 1) (hb : d309431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243312, d309431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243312, d309431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243313 q = 1) (hb : d309432 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243313, d309432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243313, d309432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243314 q = 1) (hb : d309433 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243314, d309433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243314, d309433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103555 (p : Pattern) (ha : d243320 p = 1) (hb : d309439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243284 q = 1) (hb : d309408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243284, d309408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103548 q ha hb
    | true =>
      simp only [d243284, d309408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103550 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243290 q = 1) (hb : d309409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243290, d309409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243290, d309409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d243315 q = 1) (hb : d309434 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243315, d309434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103554 q ha hb
    | true =>
      simp only [d243315, d309434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243316 q = 1) (hb : d309435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243316, d309435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243316, d309435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243317 q = 1) (hb : d309436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243317, d309436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243317, d309436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243318 q = 1) (hb : d309437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243318, d309437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243318, d309437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243319 q = 1) (hb : d309438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243319, d309438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243319, d309438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243320 q = 1) (hb : d309439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243320, d309439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243320, d309439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro103556 (p : Pattern) (ha : d243288 p = 1) (hb : d309444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243278 q = 1) (hb : d309402 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d243278, d309402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103549 q ha hb
    | true =>
      simp only [d243278, d309402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243279 q = 1) (hb : d309403 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d243279, d309403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243279, d309403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243285 q = 1) (hb : d309441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d243285, d309441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243285, d309441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243286 q = 1) (hb : d309442 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d243286, d309442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243286, d309442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243287 q = 1) (hb : d309443 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d243287, d309443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243287, d309443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243288 q = 1) (hb : d309444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243288, d309444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243288, d309444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103557 (p : Pattern) (ha : d243327 p = 1) (hb : d309450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243322 q = 1) (hb : d309445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243322, d309445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103556 q ha hb
    | true =>
      simp only [d243322, d309445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243323 q = 1) (hb : d309446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243323, d309446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243323, d309446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243324 q = 1) (hb : d309447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243324, d309447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243324, d309447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243325 q = 1) (hb : d309448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243325, d309448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243325, d309448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243326 q = 1) (hb : d309449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243326, d309449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243326, d309449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243327 q = 1) (hb : d309450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243327, d309450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243327, d309450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103558 (p : Pattern) (ha : d243333 p = 1) (hb : d309456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243051 q = 1) (hb : d309184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243051, d309184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243051, d309184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103509 q ha hb
  have h2 (q : Pattern) (ha : d243052 q = 1) (hb : d309185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243052, d309185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243052, d309185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243061 q = 1) (hb : d309194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243061, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103509 q ha hb
    | true =>
      simp only [d243061, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103512 q ha hb
  have h4 (q : Pattern) (ha : d243062 q = 1) (hb : d309195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243062, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243062, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243063 q = 1) (hb : d309196 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243063, d309196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243063, d309196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243173 q = 1) (hb : d309301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243173, d309301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103529 q ha hb
    | true =>
      simp only [d243173, d309301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103536 q ha hb
  have h7 (q : Pattern) (ha : d243186 q = 1) (hb : d309314 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243186, d309314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103537 q ha hb
    | true =>
      simp only [d243186, d309314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103538 q ha hb
  have h8 (q : Pattern) (ha : d243187 q = 1) (hb : d309315 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243187, d309315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243187, d309315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243188 q = 1) (hb : d309316 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243188, d309316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243188, d309316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d243189 q = 1) (hb : d309317 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243189, d309317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243189, d309317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243193 q = 1) (hb : d309321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243193, d309321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243193, d309321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103539 q ha hb
  have h12 (q : Pattern) (ha : d243195 q = 1) (hb : d309323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243195, d309323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243195, d309323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103540 q ha hb
  have h13 (q : Pattern) (ha : d243196 q = 1) (hb : d309324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243196, d309324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243196, d309324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243197 q = 1) (hb : d309325 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243197, d309325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243197, d309325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d243198 q = 1) (hb : d309326 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243198, d309326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243198, d309326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243199 q = 1) (hb : d309327 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243199, d309327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243199, d309327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243321 q = 1) (hb : d309440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243321, d309440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243321, d309440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103555 q ha hb
  have h18 (q : Pattern) (ha : d243328 q = 1) (hb : d309451 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243328, d309451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243328, d309451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103557 q ha hb
  have h19 (q : Pattern) (ha : d243329 q = 1) (hb : d309452 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243329, d309452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243329, d309452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d243330 q = 1) (hb : d309453 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243330, d309453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243330, d309453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d243331 q = 1) (hb : d309454 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243331, d309454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d243331, d309454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d243332 q = 1) (hb : d309455 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243332, d309455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d243332, d309455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d243333 q = 1) (hb : d309456 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243333, d309456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243333, d309456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro103559 (p : Pattern) (ha : d243339 p = 1) (hb : d309462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243334 q = 1) (hb : d309457 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243334, d309457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243334, d309457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103558 q ha hb
  have h2 (q : Pattern) (ha : d243335 q = 1) (hb : d309458 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243335, d309458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243335, d309458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243336 q = 1) (hb : d309459 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243336, d309459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243336, d309459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243337 q = 1) (hb : d309460 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243337, d309460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243337, d309460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243338 q = 1) (hb : d309461 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243338, d309461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243338, d309461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243339 q = 1) (hb : d309462 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243339, d309462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243339, d309462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103560 (p : Pattern) (ha : d44444 p = 1) (hb : d243364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243349 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d35372 q = 1) (hb : d243356 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61188 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h5 (q : Pattern) (ha : d35373 q = 1) (hb : d243357 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44441 q = 1) (hb : d243361 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d243361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44441, d243361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44442 q = 1) (hb : d243362 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d243362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44442, d243362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d44443 q = 1) (hb : d243363 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d243363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44443, d243363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d44444 q = 1) (hb : d243364 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44444, d243364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44444, d243364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103561 (p : Pattern) (ha : d44459 p = 1) (hb : d243372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d243356 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61188 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h4 (q : Pattern) (ha : d35373 q = 1) (hb : d243357 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243360 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44441 q = 1) (hb : d243361 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d243361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44441, d243361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44442 q = 1) (hb : d243362 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d243362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44442, d243362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d44443 q = 1) (hb : d243363 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d243363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44443, d243363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d44451 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44451, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99136 q ha hb
  have h10 (q : Pattern) (ha : d5128 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h11 (q : Pattern) (ha : d44452 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44452, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d44453 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44453, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44454 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99136 q ha hb
    | true =>
      simp only [d44454, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d44455 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44455, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44456 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44456, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d44457 q = 1) (hb : d243370 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44457, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d44458 q = 1) (hb : d243371 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44458, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d44459 q = 1) (hb : d243372 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44459, d243372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44459, d243372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro103562 (p : Pattern) (ha : d44465 p = 1) (hb : d243378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d243365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
    | true =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44446 q = 1) (hb : d243366 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d44447 q = 1) (hb : d243367 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d243367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44447, d243367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44448 q = 1) (hb : d243368 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d243368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44448, d243368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d44449 q = 1) (hb : d243369 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, d243369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44449, d243369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44460 q = 1) (hb : d243373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
    | true =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d44461 q = 1) (hb : d243374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d44462 q = 1) (hb : d243375 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d243375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44462, d243375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44463 q = 1) (hb : d243376 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d243376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44463, d243376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d44464 q = 1) (hb : d243377 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d243377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44464, d243377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44465 q = 1) (hb : d243378 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44465, d243378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44465, d243378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro103563 (p : Pattern) (ha : d44444 p = 1) (hb : d243384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243349 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d35372 q = 1) (hb : d243356 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61188 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h5 (q : Pattern) (ha : d35373 q = 1) (hb : d243357 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243380 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44441 q = 1) (hb : d243381 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d243381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44441, d243381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d44442 q = 1) (hb : d243382 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d243382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44442, d243382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44443 q = 1) (hb : d243383 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d243383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44443, d243383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d44444 q = 1) (hb : d243384 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44444, d243384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44444, d243384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103564 (p : Pattern) (ha : d44459 p = 1) (hb : d243389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d243356 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61188 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h4 (q : Pattern) (ha : d35373 q = 1) (hb : d243357 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243380 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44441 q = 1) (hb : d243381 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d243381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44441, d243381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44442 q = 1) (hb : d243382 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d243382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44442, d243382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44443 q = 1) (hb : d243383 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d243383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44443, d243383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d44451 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44451, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99136 q ha hb
  have h11 (q : Pattern) (ha : d5128 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5128, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
  have h12 (q : Pattern) (ha : d44452 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44452, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d44453 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44453, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d44454 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99136 q ha hb
    | true =>
      simp only [d44454, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d1564 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99135 q ha hb
    | true =>
      simp only [d1564, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d44455 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44455, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44456 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d44456, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d44457 q = 1) (hb : d243370 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44457, d243370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d44458 q = 1) (hb : d243371 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44458, d243371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h21 (q : Pattern) (ha : d44459 q = 1) (hb : d243389 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44459, d243389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44459, d243389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro103565 (p : Pattern) (ha : d44467 p = 1) (hb : d243396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d243385 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103563 q ha hb
    | true =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d243386 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d243387 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d243387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, d243387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d243388 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d243388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, d243388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44460 q = 1) (hb : d243390 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
    | true =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44461 q = 1) (hb : d243391 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44462 q = 1) (hb : d243392 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d243392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d243392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44463 q = 1) (hb : d243393 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d243393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, d243393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44464 q = 1) (hb : d243394 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d243394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d243394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44460 q = 1) (hb : d243373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
    | true =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44461 q = 1) (hb : d243374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44462 q = 1) (hb : d243375 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d243375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d243375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44463 q = 1) (hb : d243376 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d243376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44463, d243376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44466 q = 1) (hb : d243395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, d243395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44466, d243395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44467 q = 1) (hb : d243396 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44467, d243396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44467, d243396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103566 (p : Pattern) (ha : d44477 p = 1) (hb : d243401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44460 q = 1) (hb : d243390 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
    | true =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44461 q = 1) (hb : d243391 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44462 q = 1) (hb : d243392 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d243392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d243392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44463 q = 1) (hb : d243393 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d243393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44463, d243393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44466 q = 1) (hb : d243400 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, d243400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44466, d243400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44472 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99142 q ha hb
    | true =>
      simp only [d44472, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44473 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44473, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44474 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44474, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44474, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44475 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44475, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44475, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44476 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44476, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44476, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44477 q = 1) (hb : d243401 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44477, d243401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44477, d243401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103567 (p : Pattern) (ha : d44484 p = 1) (hb : d243408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44468 q = 1) (hb : d243397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d243397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103562 q ha hb
    | true =>
      simp only [d44468, d243397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103565 q ha hb
  have h2 (q : Pattern) (ha : d44469 q = 1) (hb : d243398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d243398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d243398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44470 q = 1) (hb : d243399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d243399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d243399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44478 q = 1) (hb : d243402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103565 q ha hb
    | true =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103566 q ha hb
  have h5 (q : Pattern) (ha : d44479 q = 1) (hb : d243403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44480 q = 1) (hb : d243404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44481 q = 1) (hb : d243405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d243405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, d243405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44482 q = 1) (hb : d243406 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, d243406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44482, d243406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44483 q = 1) (hb : d243407 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44483, d243407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44483, d243407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44484 q = 1) (hb : d243408 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44484, d243408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44484, d243408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro103568 (p : Pattern) (ha : d44488 p = 1) (hb : d243412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44478 q = 1) (hb : d243402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103565 q ha hb
    | true =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103566 q ha hb
  have h2 (q : Pattern) (ha : d44479 q = 1) (hb : d243403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44480 q = 1) (hb : d243404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44482 q = 1) (hb : d243406 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, d243406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44482, d243406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44487 q = 1) (hb : d243411 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44487, d243411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44487, d243411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44488 q = 1) (hb : d243412 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44488, d243412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44488, d243412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103569 (p : Pattern) (ha : d44494 p = 1) (hb : d243418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d243415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d243416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44493 q = 1) (hb : d243417 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, d243417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, d243417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44494 q = 1) (hb : d243418 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44494, d243418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44494, d243418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103570 (p : Pattern) (ha : d44498 p = 1) (hb : d243422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d243419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d243420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44497 q = 1) (hb : d243421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, d243421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, d243421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44498 q = 1) (hb : d243422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44498, d243422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44498, d243422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103571 (p : Pattern) (ha : d44504 p = 1) (hb : d243428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d243423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103569 q ha hb
    | true =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103570 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d243424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d243424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d243424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d243425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d243425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d243425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d243426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d243426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d243426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d243427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d243427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d243427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44504 q = 1) (hb : d243428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d243428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d243428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103572 (p : Pattern) (ha : d44507 p = 1) (hb : d243431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d243415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d243416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44493 q = 1) (hb : d243417 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, d243417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, d243417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44507 q = 1) (hb : d243431 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44507, d243431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44507, d243431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro103573 (p : Pattern) (ha : d44508 p = 1) (hb : d243432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d243419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d243420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44497 q = 1) (hb : d243421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, d243421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, d243421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44508 q = 1) (hb : d243432 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44508, d243432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44508, d243432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103574 (p : Pattern) (ha : d44514 p = 1) (hb : d243438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d243423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103569 q ha hb
    | true =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103570 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d243424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d243424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d243424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d243425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d243425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d243425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d243426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d243426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d243426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d243427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d243427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d243427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44509 q = 1) (hb : d243433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d243433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103572 q ha hb
    | true =>
      simp only [d44509, d243433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103573 q ha hb
  have h7 (q : Pattern) (ha : d44510 q = 1) (hb : d243434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d243434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44510, d243434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44511 q = 1) (hb : d243435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d243435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44511, d243435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44512 q = 1) (hb : d243436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d243436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d243436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44513 q = 1) (hb : d243437 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d243437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d243437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44514 q = 1) (hb : d243438 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d243438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44514, d243438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103575 (p : Pattern) (ha : d44665 p = 1) (hb : d243544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d243423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103569 q ha hb
    | true =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103570 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d243424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d243424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d243424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d243425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d243425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d243425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d243426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d243426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d243426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d243427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d243427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d243427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44660 q = 1) (hb : d243539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, d243539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103570 q ha hb
    | true =>
      simp only [d44660, d243539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44661 q = 1) (hb : d243540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, d243540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44661, d243540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44662 q = 1) (hb : d243541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, d243541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44662, d243541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44663 q = 1) (hb : d243542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, d243542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44663, d243542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44664 q = 1) (hb : d243543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, d243543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44664, d243543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44665 q = 1) (hb : d243544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44665, d243544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44665, d243544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103576 (p : Pattern) (ha : d44671 p = 1) (hb : d243550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44660 q = 1) (hb : d243539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, d243539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103570 q ha hb
    | true =>
      simp only [d44660, d243539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44661 q = 1) (hb : d243540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, d243540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44661, d243540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44662 q = 1) (hb : d243541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, d243541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44662, d243541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44663 q = 1) (hb : d243542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, d243542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44663, d243542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44664 q = 1) (hb : d243543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, d243543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44664, d243543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44666 q = 1) (hb : d243545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, d243545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103573 q ha hb
    | true =>
      simp only [d44666, d243545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44667 q = 1) (hb : d243546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, d243546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44667, d243546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44668 q = 1) (hb : d243547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, d243547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44668, d243547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44669 q = 1) (hb : d243548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, d243548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44669, d243548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44670 q = 1) (hb : d243549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, d243549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44670, d243549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44671 q = 1) (hb : d243550 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44671, d243550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44671, d243550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103577 (p : Pattern) (ha : d44680 p = 1) (hb : d243559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44666 q = 1) (hb : d243545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, d243545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103573 q ha hb
    | true =>
      simp only [d44666, d243545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44667 q = 1) (hb : d243546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, d243546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44667, d243546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44668 q = 1) (hb : d243547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, d243547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44668, d243547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44669 q = 1) (hb : d243548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, d243548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44669, d243548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44670 q = 1) (hb : d243549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, d243549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44670, d243549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44680 q = 1) (hb : d243559 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44680, d243559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44680, d243559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103578 (p : Pattern) (ha : d44702 p = 1) (hb : d243600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d243591 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d243591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, d243591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103563 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d243385 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103563 q ha hb
    | true =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d243592 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d243592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, d243592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d243386 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d243593 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d243593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, d243593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d243594 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d243594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, d243594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44692 q = 1) (hb : d243595 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d243595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d243595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
  have h8 (q : Pattern) (ha : d44460 q = 1) (hb : d243390 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
    | true =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44693 q = 1) (hb : d243596 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d243596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, d243596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44461 q = 1) (hb : d243391 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44694 q = 1) (hb : d243597 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d243597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, d243597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44695 q = 1) (hb : d243598 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d243598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, d243598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44696 q = 1) (hb : d243599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d243599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d243599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44692 q = 1) (hb : d243576 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d243576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d243576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
  have h15 (q : Pattern) (ha : d44460 q = 1) (hb : d243373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
    | true =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44693 q = 1) (hb : d243577 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d243577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44693, d243577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44461 q = 1) (hb : d243374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d44694 q = 1) (hb : d243578 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d243578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44694, d243578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d44695 q = 1) (hb : d243579 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d243579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44695, d243579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d44701 q = 1) (hb : d243585 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d243585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44701, d243585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d44702 q = 1) (hb : d243600 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44702, d243600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44702, d243600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro103579 (p : Pattern) (ha : d44712 p = 1) (hb : d243605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44692 q = 1) (hb : d243595 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d243595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d243595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
  have h2 (q : Pattern) (ha : d44460 q = 1) (hb : d243390 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
    | true =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44693 q = 1) (hb : d243596 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d243596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44693, d243596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44461 q = 1) (hb : d243391 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44694 q = 1) (hb : d243597 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d243597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44694, d243597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44695 q = 1) (hb : d243598 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d243598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44695, d243598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44701 q = 1) (hb : d243604 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d243604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44701, d243604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44707 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44707, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44707, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99142 q ha hb
  have h9 (q : Pattern) (ha : d44472 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99142 q ha hb
    | true =>
      simp only [d44472, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44708 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44708, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44708, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44473 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44473, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44709 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44709, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44709, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44710 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44710, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44710, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44711 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44711, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44711, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44712 q = 1) (hb : d243605 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44712, d243605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44712, d243605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103580 (p : Pattern) (ha : d44731 p = 1) (hb : d243624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44713 q = 1) (hb : d243606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103578 q ha hb
    | true =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103579 q ha hb
  have h2 (q : Pattern) (ha : d44714 q = 1) (hb : d243607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44715 q = 1) (hb : d243608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44721 q = 1) (hb : d243614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d243614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44721, d243614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44730 q = 1) (hb : d243623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44730, d243623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44730, d243623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44731 q = 1) (hb : d243624 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44731, d243624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44731, d243624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103581 (p : Pattern) (ha : d44813 p = 1) (hb : d243635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44732 q = 1) (hb : d243625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d243625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103580 q ha hb
    | true =>
      simp only [d44732, d243625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44733 q = 1) (hb : d243626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d243626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d243626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44810 q = 1) (hb : d243632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44810, d243632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44810, d243632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44811 q = 1) (hb : d243633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44811, d243633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44811, d243633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44812 q = 1) (hb : d243634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44812, d243634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44812, d243634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44813 q = 1) (hb : d243635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44813, d243635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44813, d243635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103582 (p : Pattern) (ha : d44819 p = 1) (hb : d243674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44814 q = 1) (hb : d243669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44814, d243669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103581 q ha hb
    | true =>
      simp only [d44814, d243669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44815 q = 1) (hb : d243670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44815, d243670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44815, d243670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44816 q = 1) (hb : d243671 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44816, d243671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44816, d243671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44817 q = 1) (hb : d243672 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44817, d243672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44817, d243672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44818 q = 1) (hb : d243673 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44818, d243673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44818, d243673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44819 q = 1) (hb : d243674 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44819, d243674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44819, d243674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103583 (p : Pattern) (ha : d44519 p = 1) (hb : d243443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d243415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d243416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44518 q = 1) (hb : d243442 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, d243442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44518, d243442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44519 q = 1) (hb : d243443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44519, d243443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44519, d243443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103584 (p : Pattern) (ha : d44521 p = 1) (hb : d243445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d243419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d243420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44520 q = 1) (hb : d243444 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, d243444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44520, d243444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44521 q = 1) (hb : d243445 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44521, d243445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44521, d243445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103585 (p : Pattern) (ha : d44528 p = 1) (hb : d243452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d243415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44526 q = 1) (hb : d243450 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, d243450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44526, d243450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44527 q = 1) (hb : d243451 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, d243451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, d243451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44528 q = 1) (hb : d243452 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44528, d243452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44528, d243452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103586 (p : Pattern) (ha : d44531 p = 1) (hb : d243455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d243419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44529 q = 1) (hb : d243453 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, d243453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44529, d243453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44530 q = 1) (hb : d243454 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, d243454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, d243454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44531 q = 1) (hb : d243455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44531, d243455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44531, d243455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103587 (p : Pattern) (ha : d44467 p = 1) (hb : d243464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d243365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
    | true =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d243366 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d243367 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d243367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, d243367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d243368 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d243368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, d243368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44460 q = 1) (hb : d243373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
    | true =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44461 q = 1) (hb : d243374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44462 q = 1) (hb : d243375 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d243375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d243375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44463 q = 1) (hb : d243376 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d243376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, d243376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44464 q = 1) (hb : d243377 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d243377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d243377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44466 q = 1) (hb : d243395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, d243395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44466, d243395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44467 q = 1) (hb : d243464 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44467, d243464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44467, d243464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103588 (p : Pattern) (ha : d44535 p = 1) (hb : d243460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243459 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44445 q = 1) (hb : d243365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
    | true =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d243366 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d44447 q = 1) (hb : d243367 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d243367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44447, d243367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44448 q = 1) (hb : d243368 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d243368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44448, d243368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d44449 q = 1) (hb : d243369 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, d243369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44449, d243369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44535 q = 1) (hb : d243460 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44535, d243460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44535, d243460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103589 (p : Pattern) (ha : d44541 p = 1) (hb : d243470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44536 q = 1) (hb : d243461 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44536, d243461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103588 q ha hb
    | true =>
      simp only [d44536, d243461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103562 q ha hb
  have h2 (q : Pattern) (ha : d44537 q = 1) (hb : d243462 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44537, d243462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44537, d243462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44538 q = 1) (hb : d243463 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44538, d243463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44538, d243463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44468 q = 1) (hb : d243465 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d243465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103562 q ha hb
    | true =>
      simp only [d44468, d243465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103587 q ha hb
  have h5 (q : Pattern) (ha : d44469 q = 1) (hb : d243466 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d243466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d243466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44470 q = 1) (hb : d243467 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d243467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d243467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44539 q = 1) (hb : d243468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44539, d243468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44539, d243468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44468 q = 1) (hb : d243397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d243397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103562 q ha hb
    | true =>
      simp only [d44468, d243397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103565 q ha hb
  have h9 (q : Pattern) (ha : d44469 q = 1) (hb : d243398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d243398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d243398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44470 q = 1) (hb : d243399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d243399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d243399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44478 q = 1) (hb : d243402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103565 q ha hb
    | true =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103566 q ha hb
  have h12 (q : Pattern) (ha : d44479 q = 1) (hb : d243403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44480 q = 1) (hb : d243404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44481 q = 1) (hb : d243405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d243405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44481, d243405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d44540 q = 1) (hb : d243469 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44540, d243469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44540, d243469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44541 q = 1) (hb : d243470 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44541, d243470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44541, d243470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro103590 (p : Pattern) (ha : d44547 p = 1) (hb : d243476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44542 q = 1) (hb : d243471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, d243471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103589 q ha hb
    | true =>
      simp only [d44542, d243471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44543 q = 1) (hb : d243472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, d243472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44543, d243472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44544 q = 1) (hb : d243473 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, d243473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, d243473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44545 q = 1) (hb : d243474 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, d243474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, d243474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44546 q = 1) (hb : d243475 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, d243475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, d243475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44547 q = 1) (hb : d243476 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44547, d243476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44547, d243476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103591 (p : Pattern) (ha : d44609 p = 1) (hb : d243482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d243356 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61188 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h4 (q : Pattern) (ha : d35373 q = 1) (hb : d243357 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44441 q = 1) (hb : d243479 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d243479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44441, d243479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d44442 q = 1) (hb : d243480 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d243480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44442, d243480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d44443 q = 1) (hb : d243481 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d243481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44443, d243481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d44609 q = 1) (hb : d243482 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44609, d243482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44609, d243482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro103592 (p : Pattern) (ha : d44615 p = 1) (hb : d243488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d243385 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103563 q ha hb
    | true =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d243386 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d243387 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, d243387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, d243387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d243388 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, d243388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, d243388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44460 q = 1) (hb : d243390 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
    | true =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44461 q = 1) (hb : d243391 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44462 q = 1) (hb : d243392 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d243392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d243392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44463 q = 1) (hb : d243393 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d243393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, d243393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44464 q = 1) (hb : d243394 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d243394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d243394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44610 q = 1) (hb : d243483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d243483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103591 q ha hb
    | true =>
      simp only [d44610, d243483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44611 q = 1) (hb : d243484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d243484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44611, d243484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44612 q = 1) (hb : d243485 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, d243485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44612, d243485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44613 q = 1) (hb : d243486 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, d243486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44613, d243486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44614 q = 1) (hb : d243487 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, d243487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44614, d243487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44615 q = 1) (hb : d243488 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44615, d243488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44615, d243488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103593 (p : Pattern) (ha : d44609 p = 1) (hb : d243492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d243356 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, d243356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61188 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h4 (q : Pattern) (ha : d35373 q = 1) (hb : d243357 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, d243357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44441 q = 1) (hb : d243489 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, d243489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44441, d243489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44442 q = 1) (hb : d243490 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, d243490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44442, d243490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44443 q = 1) (hb : d243491 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, d243491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44443, d243491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d44609 q = 1) (hb : d243492 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44609, d243492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44609, d243492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103594 (p : Pattern) (ha : d44616 p = 1) (hb : d243498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44610 q = 1) (hb : d243493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d243493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103593 q ha hb
    | true =>
      simp only [d44610, d243493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44611 q = 1) (hb : d243494 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d243494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44611, d243494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44612 q = 1) (hb : d243495 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, d243495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44612, d243495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44613 q = 1) (hb : d243496 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, d243496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44613, d243496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44614 q = 1) (hb : d243497 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, d243497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44614, d243497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44616 q = 1) (hb : d243498 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44616, d243498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44616, d243498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103595 (p : Pattern) (ha : d44622 p = 1) (hb : d243504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44468 q = 1) (hb : d243397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d243397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103562 q ha hb
    | true =>
      simp only [d44468, d243397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103565 q ha hb
  have h2 (q : Pattern) (ha : d44469 q = 1) (hb : d243398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d243398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d243398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44470 q = 1) (hb : d243399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d243399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d243399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44478 q = 1) (hb : d243402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103565 q ha hb
    | true =>
      simp only [d44478, d243402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103566 q ha hb
  have h5 (q : Pattern) (ha : d44479 q = 1) (hb : d243403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d243403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44480 q = 1) (hb : d243404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d243404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44481 q = 1) (hb : d243405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d243405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, d243405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44617 q = 1) (hb : d243499 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44617, d243499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103592 q ha hb
    | true =>
      simp only [d44617, d243499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103594 q ha hb
  have h9 (q : Pattern) (ha : d44618 q = 1) (hb : d243500 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44618, d243500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44618, d243500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44619 q = 1) (hb : d243501 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44619, d243501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44619, d243501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44620 q = 1) (hb : d243502 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44620, d243502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44620, d243502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44621 q = 1) (hb : d243503 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44621, d243503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44621, d243503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44622 q = 1) (hb : d243504 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44622, d243504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44622, d243504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro103596 (p : Pattern) (ha : d44628 p = 1) (hb : d243510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44623 q = 1) (hb : d243505 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, d243505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103595 q ha hb
    | true =>
      simp only [d44623, d243505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44624 q = 1) (hb : d243506 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, d243506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44624, d243506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44625 q = 1) (hb : d243507 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, d243507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, d243507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44626 q = 1) (hb : d243508 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, d243508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, d243508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44627 q = 1) (hb : d243509 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, d243509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, d243509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44628 q = 1) (hb : d243510 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44628, d243510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44628, d243510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103597 (p : Pattern) (ha : d243516 p = 1) (hb : d309471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44522 q = 1) (hb : d243446 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, d243446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103583 q ha hb
    | true =>
      simp only [d44522, d243446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103584 q ha hb
  have h2 (q : Pattern) (ha : d44523 q = 1) (hb : d243447 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, d243447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44523, d243447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44524 q = 1) (hb : d243448 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, d243448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, d243448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44525 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, d243449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44525, d243449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44532 q = 1) (hb : d243456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, d243456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103585 q ha hb
    | true =>
      simp only [d44532, d243456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103586 q ha hb
  have h6 (q : Pattern) (ha : d44533 q = 1) (hb : d243457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, d243457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44533, d243457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44534 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, d243458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, d243458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44548 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, d243477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103590 q ha hb
    | true =>
      simp only [d44548, d243477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103569 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243423 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d243478 q = 1) (hb : d309467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d243478, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d44629 q = 1) (hb : d243511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, d243511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103596 q ha hb
    | true =>
      simp only [d44629, d243511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44630 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, d243512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44630, d243512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d243513 q = 1) (hb : d309468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243513, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d243514 q = 1) (hb : d309469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d243514, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243515 q = 1) (hb : d309470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243515, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243516 q = 1) (hb : d309471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243516, d309471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243516, d309471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro103598 (p : Pattern) (ha : d44635 p = 1) (hb : d243517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d243415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d243416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d243416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44518 q = 1) (hb : d243442 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, d243442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44518, d243442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44635 q = 1) (hb : d243517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44635, d243517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44635, d243517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro103599 (p : Pattern) (ha : d44636 p = 1) (hb : d243518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d243419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d243420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d243420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44520 q = 1) (hb : d243444 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, d243444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44520, d243444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44636 q = 1) (hb : d243518 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44636, d243518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44636, d243518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103600 (p : Pattern) (ha : d44641 p = 1) (hb : d243523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d243415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d243415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44526 q = 1) (hb : d243450 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, d243450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44526, d243450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44527 q = 1) (hb : d243451 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, d243451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, d243451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44641 q = 1) (hb : d243523 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44641, d243523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44641, d243523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro103601 (p : Pattern) (ha : d44642 p = 1) (hb : d243524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d243413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103568 q ha hb
    | true =>
      simp only [d44489, d243413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d243414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d243414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d243419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d243419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44529 q = 1) (hb : d243453 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, d243453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44529, d243453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44530 q = 1) (hb : d243454 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, d243454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, d243454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44642 q = 1) (hb : d243524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44642, d243524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44642, d243524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103602 (p : Pattern) (ha : d44646 p = 1) (hb : d243528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44542 q = 1) (hb : d243471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, d243471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103589 q ha hb
    | true =>
      simp only [d44542, d243471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44543 q = 1) (hb : d243472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, d243472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44543, d243472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44485 q = 1) (hb : d243409 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103567 q ha hb
    | true =>
      simp only [d44485, d243409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44486 q = 1) (hb : d243410 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d243410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44544 q = 1) (hb : d243473 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, d243473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, d243473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44545 q = 1) (hb : d243474 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, d243474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, d243474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44546 q = 1) (hb : d243475 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, d243475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, d243475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44646 q = 1) (hb : d243528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44646, d243528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44646, d243528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro103603 (p : Pattern) (ha : d44652 p = 1) (hb : d243531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44623 q = 1) (hb : d243505 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, d243505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103595 q ha hb
    | true =>
      simp only [d44623, d243505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44624 q = 1) (hb : d243506 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, d243506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44624, d243506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44625 q = 1) (hb : d243507 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, d243507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, d243507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44626 q = 1) (hb : d243508 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, d243508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, d243508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44627 q = 1) (hb : d243509 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, d243509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, d243509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44652 q = 1) (hb : d243531 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44652, d243531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44652, d243531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103604 (p : Pattern) (ha : d243537 p = 1) (hb : d309476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44522 q = 1) (hb : d243446 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, d243446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103583 q ha hb
    | true =>
      simp only [d44522, d243446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103584 q ha hb
  have h2 (q : Pattern) (ha : d44523 q = 1) (hb : d243447 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, d243447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44523, d243447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44524 q = 1) (hb : d243448 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, d243448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, d243448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44525 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, d243449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44525, d243449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44532 q = 1) (hb : d243456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, d243456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103585 q ha hb
    | true =>
      simp only [d44532, d243456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103586 q ha hb
  have h6 (q : Pattern) (ha : d44533 q = 1) (hb : d243457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, d243457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44533, d243457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44534 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, d243458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, d243458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44548 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, d243477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103590 q ha hb
    | true =>
      simp only [d44548, d243477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103569 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243423 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d243478 q = 1) (hb : d309467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d243478, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d44629 q = 1) (hb : d243511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, d243511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103596 q ha hb
    | true =>
      simp only [d44629, d243511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44630 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, d243512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44630, d243512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d243513 q = 1) (hb : d309468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243513, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d243514 q = 1) (hb : d309469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d243514, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243515 q = 1) (hb : d309470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243515, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44637 q = 1) (hb : d243519 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44637, d243519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103598 q ha hb
    | true =>
      simp only [d44637, d243519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103599 q ha hb
  have h17 (q : Pattern) (ha : d44638 q = 1) (hb : d243520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44638, d243520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44638, d243520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44639 q = 1) (hb : d243521 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44639, d243521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d44639, d243521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d44640 q = 1) (hb : d243522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44640, d243522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44640, d243522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d44643 q = 1) (hb : d243525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44643, d243525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103600 q ha hb
    | true =>
      simp only [d44643, d243525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103601 q ha hb
  have h21 (q : Pattern) (ha : d44644 q = 1) (hb : d243526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44644, d243526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44644, d243526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d44645 q = 1) (hb : d243527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44645, d243527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d44645, d243527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d44647 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, d243529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103602 q ha hb
    | true =>
      simp only [d44647, d243529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103572 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d243433 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d243530 q = 1) (hb : d309472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d243530, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d44653 q = 1) (hb : d243532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, d243532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103603 q ha hb
    | true =>
      simp only [d44653, d243532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d44654 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, d243533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d44654, d243533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d243534 q = 1) (hb : d309473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d243534, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d243535 q = 1) (hb : d309474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243535, d309474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d243535, d309474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d243536 q = 1) (hb : d309475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243536, d309475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d243536, d309475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d243537 q = 1) (hb : d309476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243537, d309476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243537, d309476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro103605 (p : Pattern) (ha : d243557 p = 1) (hb : d309483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44647 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, d243529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103602 q ha hb
    | true =>
      simp only [d44647, d243529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243530 q = 1) (hb : d309472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243530, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d44653 q = 1) (hb : d243532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, d243532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103603 q ha hb
    | true =>
      simp only [d44653, d243532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44654 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, d243533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44654, d243533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d243534 q = 1) (hb : d309473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243534, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243555 q = 1) (hb : d309481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243555, d309481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243555, d309481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243556 q = 1) (hb : d309482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243556, d309482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243556, d309482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243557 q = 1) (hb : d309483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243557, d309483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243557, d309483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro103606 (p : Pattern) (ha : d44691 p = 1) (hb : d243575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243569 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243568 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44686 q = 1) (hb : d243570 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d243570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44686, d243570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
  have h4 (q : Pattern) (ha : d44445 q = 1) (hb : d243365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
    | true =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d44687 q = 1) (hb : d243571 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d243571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44687, d243571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44446 q = 1) (hb : d243366 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d44688 q = 1) (hb : d243572 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d243572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44688, d243572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44689 q = 1) (hb : d243573 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d243573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44689, d243573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d44690 q = 1) (hb : d243574 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, d243574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44690, d243574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44691 q = 1) (hb : d243575 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44691, d243575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44691, d243575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103607 (p : Pattern) (ha : d44697 p = 1) (hb : d243581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243568 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44686 q = 1) (hb : d243570 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d243570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44686, d243570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
  have h3 (q : Pattern) (ha : d44445 q = 1) (hb : d243365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
    | true =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d44687 q = 1) (hb : d243571 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d243571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44687, d243571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44446 q = 1) (hb : d243366 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d44688 q = 1) (hb : d243572 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d243572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44688, d243572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44689 q = 1) (hb : d243573 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d243573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44689, d243573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d44690 q = 1) (hb : d243574 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, d243574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44690, d243574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44692 q = 1) (hb : d243576 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d243576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44692, d243576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
  have h10 (q : Pattern) (ha : d44460 q = 1) (hb : d243373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
    | true =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d44693 q = 1) (hb : d243577 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d243577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44693, d243577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44461 q = 1) (hb : d243374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d44694 q = 1) (hb : d243578 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d243578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44694, d243578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44695 q = 1) (hb : d243579 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d243579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44695, d243579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d44696 q = 1) (hb : d243580 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d243580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44696, d243580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44697 q = 1) (hb : d243581 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44697, d243581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44697, d243581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro103608 (p : Pattern) (ha : d44702 p = 1) (hb : d243586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d243570 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d243570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, d243570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d243365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103560 q ha hb
    | true =>
      simp only [d44445, d243365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d243571 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d243571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, d243571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d243366 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d243366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d243572 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d243572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, d243572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d243573 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d243573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, d243573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44692 q = 1) (hb : d243576 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d243576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d243576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
  have h8 (q : Pattern) (ha : d44460 q = 1) (hb : d243373 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103561 q ha hb
    | true =>
      simp only [d44460, d243373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44693 q = 1) (hb : d243577 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d243577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, d243577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44461 q = 1) (hb : d243374 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, d243374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44694 q = 1) (hb : d243578 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d243578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, d243578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44695 q = 1) (hb : d243579 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d243579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, d243579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44696 q = 1) (hb : d243580 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d243580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d243580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44701 q = 1) (hb : d243585 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d243585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44701, d243585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44702 q = 1) (hb : d243586 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44702, d243586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44702, d243586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103609 (p : Pattern) (ha : d44718 p = 1) (hb : d243611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44698 q = 1) (hb : d243582 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44698, d243582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103606 q ha hb
    | true =>
      simp only [d44698, d243582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103607 q ha hb
  have h2 (q : Pattern) (ha : d44699 q = 1) (hb : d243583 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44699, d243583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44699, d243583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44700 q = 1) (hb : d243584 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44700, d243584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44700, d243584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44703 q = 1) (hb : d243587 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d243587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103607 q ha hb
    | true =>
      simp only [d44703, d243587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103608 q ha hb
  have h5 (q : Pattern) (ha : d44704 q = 1) (hb : d243588 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d243588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d243588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44705 q = 1) (hb : d243589 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d243589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d243589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44706 q = 1) (hb : d243590 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44706, d243590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44706, d243590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44703 q = 1) (hb : d243601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d243601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103607 q ha hb
    | true =>
      simp only [d44703, d243601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103578 q ha hb
  have h9 (q : Pattern) (ha : d44704 q = 1) (hb : d243602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d243602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d243602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44705 q = 1) (hb : d243603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d243603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d243603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44713 q = 1) (hb : d243606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103578 q ha hb
    | true =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103579 q ha hb
  have h12 (q : Pattern) (ha : d44714 q = 1) (hb : d243607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44715 q = 1) (hb : d243608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44716 q = 1) (hb : d243609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d243609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44716, d243609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d44717 q = 1) (hb : d243610 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44717, d243610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44717, d243610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44718 q = 1) (hb : d243611 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44718, d243611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44718, d243611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro103610 (p : Pattern) (ha : d44723 p = 1) (hb : d243616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44703 q = 1) (hb : d243601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d243601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103607 q ha hb
    | true =>
      simp only [d44703, d243601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103578 q ha hb
  have h2 (q : Pattern) (ha : d44704 q = 1) (hb : d243602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d243602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d243602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44705 q = 1) (hb : d243603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d243603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d243603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44713 q = 1) (hb : d243606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103578 q ha hb
    | true =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103579 q ha hb
  have h5 (q : Pattern) (ha : d44714 q = 1) (hb : d243607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44715 q = 1) (hb : d243608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44716 q = 1) (hb : d243609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d243609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, d243609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44721 q = 1) (hb : d243614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d243614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44721, d243614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44722 q = 1) (hb : d243615 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44722, d243615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44722, d243615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44723 q = 1) (hb : d243616 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44723, d243616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44723, d243616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro103611 (p : Pattern) (ha : d44729 p = 1) (hb : d243622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44719 q = 1) (hb : d243612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44719, d243612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103609 q ha hb
    | true =>
      simp only [d44719, d243612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44720 q = 1) (hb : d243613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44720, d243613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44720, d243613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44724 q = 1) (hb : d243617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, d243617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103610 q ha hb
    | true =>
      simp only [d44724, d243617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44725 q = 1) (hb : d243618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, d243618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44725, d243618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44726 q = 1) (hb : d243619 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44726, d243619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44726, d243619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44727 q = 1) (hb : d243620 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44727, d243620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44727, d243620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44728 q = 1) (hb : d243621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44728, d243621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44728, d243621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44729 q = 1) (hb : d243622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44729, d243622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44729, d243622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro103612 (p : Pattern) (ha : d44737 p = 1) (hb : d243630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44724 q = 1) (hb : d243617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, d243617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103610 q ha hb
    | true =>
      simp only [d44724, d243617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44725 q = 1) (hb : d243618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, d243618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44725, d243618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44732 q = 1) (hb : d243625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d243625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103580 q ha hb
    | true =>
      simp only [d44732, d243625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44733 q = 1) (hb : d243626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d243626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d243626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44734 q = 1) (hb : d243627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44734, d243627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44734, d243627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44735 q = 1) (hb : d243628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44735, d243628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44735, d243628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44736 q = 1) (hb : d243629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44736, d243629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44736, d243629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44737 q = 1) (hb : d243630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44737, d243630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44737, d243630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro103613 (p : Pattern) (ha : d44789 p = 1) (hb : d243643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d243591 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, d243591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, d243591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103563 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d243385 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103563 q ha hb
    | true =>
      simp only [d44445, d243385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d243592 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, d243592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, d243592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d243386 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, d243386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d243593 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, d243593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, d243593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d243594 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, d243594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, d243594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44692 q = 1) (hb : d243595 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d243595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d243595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
  have h8 (q : Pattern) (ha : d44460 q = 1) (hb : d243390 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103564 q ha hb
    | true =>
      simp only [d44460, d243390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44693 q = 1) (hb : d243596 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d243596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, d243596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44461 q = 1) (hb : d243391 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, d243391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44694 q = 1) (hb : d243597 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d243597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, d243597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44695 q = 1) (hb : d243598 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d243598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, d243598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44696 q = 1) (hb : d243599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d243599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d243599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44784 q = 1) (hb : d243638 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, d243638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44784, d243638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103591 q ha hb
  have h15 (q : Pattern) (ha : d44610 q = 1) (hb : d243483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d243483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103591 q ha hb
    | true =>
      simp only [d44610, d243483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44785 q = 1) (hb : d243639 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, d243639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44785, d243639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44611 q = 1) (hb : d243484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d243484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44611, d243484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d44786 q = 1) (hb : d243640 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, d243640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44786, d243640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d44787 q = 1) (hb : d243641 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, d243641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44787, d243641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d44788 q = 1) (hb : d243642 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, d243642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44788, d243642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d44789 q = 1) (hb : d243643 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44789, d243643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44789, d243643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro103614 (p : Pattern) (ha : d44790 p = 1) (hb : d243649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44784 q = 1) (hb : d243644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, d243644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44784, d243644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103593 q ha hb
  have h2 (q : Pattern) (ha : d44610 q = 1) (hb : d243493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, d243493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103593 q ha hb
    | true =>
      simp only [d44610, d243493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44785 q = 1) (hb : d243645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, d243645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44785, d243645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44611 q = 1) (hb : d243494 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, d243494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44611, d243494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44786 q = 1) (hb : d243646 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, d243646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44786, d243646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44787 q = 1) (hb : d243647 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, d243647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44787, d243647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44788 q = 1) (hb : d243648 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, d243648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44788, d243648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44790 q = 1) (hb : d243649 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44790, d243649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44790, d243649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro103615 (p : Pattern) (ha : d44796 p = 1) (hb : d243655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44703 q = 1) (hb : d243601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d243601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103607 q ha hb
    | true =>
      simp only [d44703, d243601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103578 q ha hb
  have h2 (q : Pattern) (ha : d44704 q = 1) (hb : d243602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d243602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d243602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44705 q = 1) (hb : d243603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d243603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d243603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44713 q = 1) (hb : d243606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103578 q ha hb
    | true =>
      simp only [d44713, d243606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103579 q ha hb
  have h5 (q : Pattern) (ha : d44714 q = 1) (hb : d243607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d243607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44715 q = 1) (hb : d243608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d243608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44716 q = 1) (hb : d243609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d243609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, d243609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44791 q = 1) (hb : d243650 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44791, d243650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103613 q ha hb
    | true =>
      simp only [d44791, d243650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103614 q ha hb
  have h9 (q : Pattern) (ha : d44792 q = 1) (hb : d243651 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44792, d243651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44792, d243651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44793 q = 1) (hb : d243652 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44793, d243652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44793, d243652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44794 q = 1) (hb : d243653 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44794, d243653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44794, d243653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44795 q = 1) (hb : d243654 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44795, d243654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44795, d243654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44796 q = 1) (hb : d243655 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44796, d243655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44796, d243655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro103616 (p : Pattern) (ha : d44802 p = 1) (hb : d243661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44797 q = 1) (hb : d243656 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44797, d243656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103615 q ha hb
    | true =>
      simp only [d44797, d243656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44798 q = 1) (hb : d243657 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44798, d243657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44798, d243657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44799 q = 1) (hb : d243658 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44799, d243658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44799, d243658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44800 q = 1) (hb : d243659 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44800, d243659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44800, d243659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44801 q = 1) (hb : d243660 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44801, d243660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44801, d243660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44802 q = 1) (hb : d243661 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44802, d243661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44802, d243661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103617 (p : Pattern) (ha : d243667 p = 1) (hb : d309493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44738 q = 1) (hb : d243631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44738, d243631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103611 q ha hb
    | true =>
      simp only [d44738, d243631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103612 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243637 q = 1) (hb : d309489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243637, d309489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243637, d309489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d44803 q = 1) (hb : d243662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44803, d243662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103616 q ha hb
    | true =>
      simp only [d44803, d243662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44804 q = 1) (hb : d243663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44804, d243663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44804, d243663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d243664 q = 1) (hb : d309490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243664, d309490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243664, d309490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243665 q = 1) (hb : d309491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243665, d309491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243665, d309491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243666 q = 1) (hb : d309492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243666, d309492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243666, d309492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243667 q = 1) (hb : d309493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243667, d309493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243667, d309493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro103618 (p : Pattern) (ha : d243680 p = 1) (hb : d309499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44505 q = 1) (hb : d243429 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44505, d243429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44505, d243429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103571 q ha hb
  have h2 (q : Pattern) (ha : d44506 q = 1) (hb : d243430 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44506, d243430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44506, d243430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44515 q = 1) (hb : d243439 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d243439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103571 q ha hb
    | true =>
      simp only [d44515, d243439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103574 q ha hb
  have h4 (q : Pattern) (ha : d44516 q = 1) (hb : d243440 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d243440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44516, d243440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44517 q = 1) (hb : d243441 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44517, d243441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44517, d243441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243538 q = 1) (hb : d309477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243538, d309477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103597 q ha hb
    | true =>
      simp only [d243538, d309477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103604 q ha hb
  have h7 (q : Pattern) (ha : d44672 q = 1) (hb : d243551 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44672, d243551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103575 q ha hb
    | true =>
      simp only [d44672, d243551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103576 q ha hb
  have h8 (q : Pattern) (ha : d243552 q = 1) (hb : d309478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243552, d309478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243552, d309478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d243553 q = 1) (hb : d309479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243553, d309479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243553, d309479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d243554 q = 1) (hb : d309480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243554, d309480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d243554, d309480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243558 q = 1) (hb : d309484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243558, d309484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243558, d309484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103605 q ha hb
  have h12 (q : Pattern) (ha : d44681 q = 1) (hb : d243560 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44681, d243560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44681, d243560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103577 q ha hb
  have h13 (q : Pattern) (ha : d243561 q = 1) (hb : d309485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243561, d309485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243561, d309485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d243562 q = 1) (hb : d309486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243562, d309486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243562, d309486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d243563 q = 1) (hb : d309487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243563, d309487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d243563, d309487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d243564 q = 1) (hb : d309488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243564, d309488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243564, d309488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243668 q = 1) (hb : d309494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243668, d309494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243668, d309494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103617 q ha hb
  have h18 (q : Pattern) (ha : d44820 q = 1) (hb : d243675 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44820, d243675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44820, d243675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103582 q ha hb
  have h19 (q : Pattern) (ha : d243676 q = 1) (hb : d309495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243676, d309495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243676, d309495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d243677 q = 1) (hb : d309496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243677, d309496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d243677, d309496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d243678 q = 1) (hb : d309497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243678, d309497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d243678, d309497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d243679 q = 1) (hb : d309498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243679, d309498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d243679, d309498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d243680 q = 1) (hb : d309499 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243680, d309499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243680, d309499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro103619 (p : Pattern) (ha : d243686 p = 1) (hb : d309505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243681 q = 1) (hb : d309500 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243681, d309500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243681, d309500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103618 q ha hb
  have h2 (q : Pattern) (ha : d243682 q = 1) (hb : d309501 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243682, d309501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243682, d309501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243683 q = 1) (hb : d309502 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243683, d309502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243683, d309502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243684 q = 1) (hb : d309503 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243684, d309503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243684, d309503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243685 q = 1) (hb : d309504 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243685, d309504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243685, d309504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243686 q = 1) (hb : d309505 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243686, d309505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243686, d309505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103620 (p : Pattern) (ha : d243692 p = 1) (hb : d309511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d308450 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d308450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103331 q ha hb
    | true =>
      simp only [d242306, d308450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103378 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d308726 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d308726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d308726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103432 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d308727 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d308727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d308727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d309092 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d309092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d309092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103494 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d309093 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d309093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d309093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d309094 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d309094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d309094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d309463 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d309463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d309463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103559 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d309464 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d309464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d309464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d309465 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d309465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d309465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d309466 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d309466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d309466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d309506 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d309506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d309506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103619 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d309507 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d309507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d309507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d309508 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d309508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d309508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d309509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d309509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d309510 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d309510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d309510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d309511 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d309511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d309511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro103621 (p : Pattern) (ha : d243698 p = 1) (hb : d309517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d309512 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d309512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103620 q ha hb
    | true =>
      simp only [d243693, d309512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d309513 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d309513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d309513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d309514 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d309514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d309514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d309515 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d309515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d309515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d309516 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d309516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d309516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d309517 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d309517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d309517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103622 (p : Pattern) (ha : d243704 p = 1) (hb : d309523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d309518 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d309518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103621 q ha hb
    | true =>
      simp only [d243699, d309518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d309519 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d309519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d309519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d309520 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d309520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d309520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d309521 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d309521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d309521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d309522 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d309522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d309522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d309523 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d309523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d309523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103623 (p : Pattern) (ha : d243710 p = 1) (hb : d309529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d309524 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d309524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103622 q ha hb
    | true =>
      simp only [d243705, d309524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d309525 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d309525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d309525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d309526 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d309526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d309526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d309527 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d309527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d309527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d309528 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d309528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d309528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d309529 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d309529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d309529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103624 (p : Pattern) (ha : d243716 p = 1) (hb : d309535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d309530 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d309530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103623 q ha hb
    | true =>
      simp only [d243711, d309530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d309531 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d309531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d309531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d309532 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d309532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d309532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d309533 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d309533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d309533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d309534 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d309534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d309534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d309535 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d309535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d309535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103625 (p : Pattern) (ha : d243722 p = 1) (hb : d309541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d309536 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d309536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103624 q ha hb
    | true =>
      simp only [d243717, d309536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d309537 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d309537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d309537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d309538 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d309538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d309538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d309539 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d309539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d309539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d309540 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d309540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d309540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d309541 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d309541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d309541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103626 (p : Pattern) (ha : d243728 p = 1) (hb : d309547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d309542 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d309542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103625 q ha hb
    | true =>
      simp only [d243723, d309542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d309543 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d309543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d309543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d309544 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d309544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d309544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d309545 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d309545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d309545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d309546 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d309546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d309546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d309547 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d309547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d309547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103627 (p : Pattern) (ha : d243734 p = 1) (hb : d309553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d309548 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d309548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103626 q ha hb
    | true =>
      simp only [d243729, d309548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d309549 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d309549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d309549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d309550 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d309550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d309550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d309551 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d309551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d309551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d309552 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d309552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d309552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d309553 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d309553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d309553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103628 (p : Pattern) (ha : d306035 p = 1) (hb : d357418 p = 1) : d309556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d306035 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42281 q = 1) (hb : d306035 q = 1) : d308006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d308006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103008 q ha hb
    | true =>
      simp only [d42281, d308006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42341 q = 1) (hb : d306035 q = 1) : d308066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42341, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42341, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42342 q = 1) (hb : d306035 q = 1) : d308067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42342, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42342, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42343 q = 1) (hb : d306035 q = 1) : d308068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42343, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42343, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42344 q = 1) (hb : d306035 q = 1) : d308069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42344, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42344, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357418 q = 1) : d309556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357418, d309556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357418, d309556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro103629 (p : Pattern) (ha : d306035 p = 1) (hb : d357428 p = 1) : d309566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d306035 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42317 q = 1) (hb : d306035 q = 1) : d308042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42317, d308042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103013 q ha hb
    | true =>
      simp only [d42317, d308042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357424 q = 1) : d309562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357424, d309562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357424, d309562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357425 q = 1) : d309563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357425, d309563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357425, d309563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357426 q = 1) : d309564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357426, d309564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357426, d309564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357427 q = 1) : d309565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357427, d309565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357427, d309565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357428 q = 1) : d309566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357428, d309566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357428, d309566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro103630 (p : Pattern) (ha : d306035 p = 1) (hb : d357434 p = 1) : d309572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42346 q = 1) (hb : d306035 q = 1) : d308071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42346, d308071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103016 q ha hb
    | true =>
      simp only [d42346, d308071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103017 q ha hb
  have h2 (q : Pattern) (ha : d42347 q = 1) (hb : d306035 q = 1) : d308072 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42347, d308072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42347, d308072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357416 q = 1) : d309554 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357416, d309554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357416, d309554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357417 q = 1) : d309555 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357417, d309555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357417, d309555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357419 q = 1) : d309557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357419, d309557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357419, d309557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103628 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357420 q = 1) : d309558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357420, d309558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357420, d309558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357421 q = 1) : d309559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357421, d309559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357421, d309559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d306035 q = 1) (hb : d357422 q = 1) : d309560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357422, d309560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357422, d309560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d306035 q = 1) (hb : d357423 q = 1) : d309561 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357423, d309561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357423, d309561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306035 q = 1) (hb : d357429 q = 1) : d309567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357429, d309567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357429, d309567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103629 q ha hb
  have h11 (q : Pattern) (ha : d306035 q = 1) (hb : d357430 q = 1) : d309568 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357430, d309568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357430, d309568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d306035 q = 1) (hb : d357431 q = 1) : d309569 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357431, d309569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357431, d309569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d306035 q = 1) (hb : d357432 q = 1) : d309570 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357432, d309570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357432, d309570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d306035 q = 1) (hb : d357433 q = 1) : d309571 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357433, d309571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357433, d309571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d306035 q = 1) (hb : d357434 q = 1) : d309572 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357434, d309572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357434, d309572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103631 (p : Pattern) (ha : d306035 p = 1) (hb : d357440 p = 1) : d309578 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d306035 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357435 q = 1) : d309573 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357435, d309573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357435, d309573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103630 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357436 q = 1) : d309574 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357436, d309574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357436, d309574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357437 q = 1) : d309575 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357437, d309575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357437, d309575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357438 q = 1) : d309576 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357438, d309576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357438, d309576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357439 q = 1) : d309577 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357439, d309577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357439, d309577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357440 q = 1) : d309578 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d309578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357440, d309578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro103632 (p : Pattern) (ha : d306035 p = 1) (hb : d357443 p = 1) : d309581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42565 q = 1) (hb : d306035 q = 1) : d308238 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42565, d308238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103047 q ha hb
    | true =>
      simp only [d42565, d308238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103048 q ha hb
  have h2 (q : Pattern) (ha : d42566 q = 1) (hb : d306035 q = 1) : d308239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42566, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42566, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42567 q = 1) (hb : d306035 q = 1) : d308240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42567, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42567, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42568 q = 1) (hb : d306035 q = 1) : d308241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42568, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42568, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42569 q = 1) (hb : d306035 q = 1) : d308242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42569, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42569, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357443 q = 1) : d309581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357443, d309581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357443, d309581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro103633 (p : Pattern) (ha : d306035 p = 1) (hb : d357454 p = 1) : d309592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357449 q = 1) : d309587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357449, d309587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103084 q hb ha
    | true =>
      simp only [d357449, d309587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103054 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357450 q = 1) : d309588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357450, d309588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357450, d309588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357451 q = 1) : d309589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357451, d309589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357451, d309589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357452 q = 1) : d309590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357452, d309590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357452, d309590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357453 q = 1) : d309591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357453, d309591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357453, d309591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357454 q = 1) : d309592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357454, d309592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357454, d309592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103634 (p : Pattern) (ha : d306035 p = 1) (hb : d357460 p = 1) : d309598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42571 q = 1) (hb : d306035 q = 1) : d308244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42571, d308244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103046 q ha hb
    | true =>
      simp only [d42571, d308244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103049 q ha hb
  have h2 (q : Pattern) (ha : d42572 q = 1) (hb : d306035 q = 1) : d308245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42572, d308245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42572, d308245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357441 q = 1) : d309579 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357441, d309579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357441, d309579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357442 q = 1) : d309580 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357442, d309580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357442, d309580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357444 q = 1) : d309582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357444, d309582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357444, d309582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103632 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357445 q = 1) : d309583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357445, d309583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357445, d309583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357446 q = 1) : d309584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357446, d309584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357446, d309584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d306035 q = 1) (hb : d357447 q = 1) : d309585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357447, d309585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357447, d309585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d306035 q = 1) (hb : d357448 q = 1) : d309586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357448, d309586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357448, d309586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306035 q = 1) (hb : d357455 q = 1) : d309593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357455, d309593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357455, d309593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103633 q ha hb
  have h11 (q : Pattern) (ha : d306035 q = 1) (hb : d357456 q = 1) : d309594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357456, d309594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357456, d309594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d306035 q = 1) (hb : d357457 q = 1) : d309595 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357457, d309595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357457, d309595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d306035 q = 1) (hb : d357458 q = 1) : d309596 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357458, d309596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357458, d309596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d306035 q = 1) (hb : d357459 q = 1) : d309597 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357459, d309597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357459, d309597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d306035 q = 1) (hb : d357460 q = 1) : d309598 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357460, d309598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357460, d309598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103635 (p : Pattern) (ha : d306035 p = 1) (hb : d357466 p = 1) : d309604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357461 q = 1) : d309599 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357461, d309599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357461, d309599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103634 q ha hb
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357462 q = 1) : d309600 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357462, d309600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357462, d309600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357463 q = 1) : d309601 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357463, d309601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357463, d309601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357464 q = 1) : d309602 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357464, d309602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357464, d309602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357465 q = 1) : d309603 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357465, d309603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357465, d309603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357466 q = 1) : d309604 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357466, d309604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357466, d309604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103636 (p : Pattern) (ha : d306035 p = 1) (hb : d357470 p = 1) : d309608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42909 q = 1) (hb : d306035 q = 1) : d308496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42909, d308496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103098 q ha hb
    | true =>
      simp only [d42909, d308496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103099 q ha hb
  have h2 (q : Pattern) (ha : d42910 q = 1) (hb : d306035 q = 1) : d308497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42910, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42910, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42911 q = 1) (hb : d306035 q = 1) : d308498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42911, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42911, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42912 q = 1) (hb : d306035 q = 1) : d308499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42912, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42912, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42913 q = 1) (hb : d306035 q = 1) : d308500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42913, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42913, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357470 q = 1) : d309608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357470, d309608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357470, d309608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro103637 (p : Pattern) (ha : d306035 p = 1) (hb : d357481 p = 1) : d309619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357476 q = 1) : d309614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357476, d309614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103140 q hb ha
    | true =>
      simp only [d357476, d309614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103107 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357477 q = 1) : d309615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357477, d309615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357477, d309615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357478 q = 1) : d309616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357478, d309616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357478, d309616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357479 q = 1) : d309617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357479, d309617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357479, d309617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357480 q = 1) : d309618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357480, d309618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357480, d309618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357481 q = 1) : d309619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357481, d309619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357481, d309619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103638 (p : Pattern) (ha : d306035 p = 1) (hb : d357487 p = 1) : d309625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42915 q = 1) (hb : d306035 q = 1) : d308502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42915, d308502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103097 q ha hb
    | true =>
      simp only [d42915, d308502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103100 q ha hb
  have h2 (q : Pattern) (ha : d42916 q = 1) (hb : d306035 q = 1) : d308503 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42916, d308503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42916, d308503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357468 q = 1) : d309606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357468, d309606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357468, d309606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357469 q = 1) : d309607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357469, d309607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357469, d309607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357471 q = 1) : d309609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357471, d309609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357471, d309609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103636 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357472 q = 1) : d309610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357472, d309610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357472, d309610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357473 q = 1) : d309611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357473, d309611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357473, d309611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d306035 q = 1) (hb : d357474 q = 1) : d309612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357474, d309612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357474, d309612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d306035 q = 1) (hb : d357475 q = 1) : d309613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357475, d309613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357475, d309613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306035 q = 1) (hb : d357482 q = 1) : d309620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357482, d309620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357482, d309620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103637 q ha hb
  have h11 (q : Pattern) (ha : d306035 q = 1) (hb : d357483 q = 1) : d309621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357483, d309621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357483, d309621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d306035 q = 1) (hb : d357484 q = 1) : d309622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357484, d309622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357484, d309622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d306035 q = 1) (hb : d357485 q = 1) : d309623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357485, d309623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357485, d309623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d306035 q = 1) (hb : d357486 q = 1) : d309624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357486, d309624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357486, d309624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d306035 q = 1) (hb : d357487 q = 1) : d309625 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357487, d309625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357487, d309625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103639 (p : Pattern) (ha : d306035 p = 1) (hb : d357493 p = 1) : d309631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357488 q = 1) : d309626 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357488, d309626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357488, d309626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103638 q ha hb
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357489 q = 1) : d309627 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357489, d309627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357489, d309627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357490 q = 1) : d309628 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357490, d309628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357490, d309628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357491 q = 1) : d309629 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357491, d309629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357491, d309629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357492 q = 1) : d309630 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357492, d309630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357492, d309630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357493 q = 1) : d309631 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357493, d309631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357493, d309631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103640 (p : Pattern) (ha : d306035 p = 1) (hb : d357498 p = 1) : d309636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43379 q = 1) (hb : d306035 q = 1) : d308818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43379, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103161 q ha hb
    | true =>
      simp only [d43379, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103162 q ha hb
  have h2 (q : Pattern) (ha : d43380 q = 1) (hb : d306035 q = 1) : d308819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43380, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43380, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43381 q = 1) (hb : d306035 q = 1) : d308820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43381, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43381, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43382 q = 1) (hb : d306035 q = 1) : d308821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43382, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43382, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43383 q = 1) (hb : d306035 q = 1) : d308822 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43383, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43383, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357498 q = 1) : d309636 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357498, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357498, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro103641 (p : Pattern) (ha : d306035 p = 1) (hb : d357509 p = 1) : d309647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357504 q = 1) : d309642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357504, d309642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103204 q hb ha
    | true =>
      simp only [d357504, d309642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103170 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357505 q = 1) : d309643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357505, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357505, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357506 q = 1) : d309644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357506, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357506, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357507 q = 1) : d309645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357507, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357507, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357508 q = 1) : d309646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357508, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357508, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357509 q = 1) : d309647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357509, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357509, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103642 (p : Pattern) (ha : d306035 p = 1) (hb : d357515 p = 1) : d309653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43385 q = 1) (hb : d306035 q = 1) : d308824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43385, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103160 q ha hb
    | true =>
      simp only [d43385, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103163 q ha hb
  have h2 (q : Pattern) (ha : d43386 q = 1) (hb : d306035 q = 1) : d308825 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43386, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43386, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357496 q = 1) : d309634 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357496, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357496, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357497 q = 1) : d309635 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357497, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357497, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357499 q = 1) : d309637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357499, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357499, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103640 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357500 q = 1) : d309638 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357500, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357500, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357501 q = 1) : d309639 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357501, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357501, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d306035 q = 1) (hb : d357502 q = 1) : d309640 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357502, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357502, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d306035 q = 1) (hb : d357503 q = 1) : d309641 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357503, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357503, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306035 q = 1) (hb : d357510 q = 1) : d309648 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357510, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357510, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103641 q ha hb
  have h11 (q : Pattern) (ha : d306035 q = 1) (hb : d357511 q = 1) : d309649 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357511, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357511, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d306035 q = 1) (hb : d357512 q = 1) : d309650 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357512, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357512, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d306035 q = 1) (hb : d357513 q = 1) : d309651 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357513, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357513, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d306035 q = 1) (hb : d357514 q = 1) : d309652 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357514, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357514, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d306035 q = 1) (hb : d357515 q = 1) : d309653 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357515, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357515, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103643 (p : Pattern) (ha : d306035 p = 1) (hb : d357521 p = 1) : d309659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357516 q = 1) : d309654 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357516, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357516, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103642 q ha hb
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357517 q = 1) : d309655 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357517, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357517, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357518 q = 1) : d309656 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357518, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357518, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357519 q = 1) : d309657 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357519, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357519, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357520 q = 1) : d309658 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357520, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357520, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357521 q = 1) : d309659 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357521, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357521, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103644 (p : Pattern) (ha : d306035 p = 1) (hb : d357527 p = 1) : d309665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43964 q = 1) (hb : d306035 q = 1) : d309188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43964, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103232 q ha hb
    | true =>
      simp only [d43964, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103233 q ha hb
  have h2 (q : Pattern) (ha : d43965 q = 1) (hb : d306035 q = 1) : d309189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43965, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43965, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43966 q = 1) (hb : d306035 q = 1) : d309190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43966, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43966, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43967 q = 1) (hb : d306035 q = 1) : d309191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43967, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43967, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43968 q = 1) (hb : d306035 q = 1) : d309192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43968, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43968, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357527 q = 1) : d309665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357527, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357527, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro103645 (p : Pattern) (ha : d306035 p = 1) (hb : d357538 p = 1) : d309676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357533 q = 1) : d309671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357533, d309671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103276 q hb ha
    | true =>
      simp only [d357533, d309671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103241 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357534 q = 1) : d309672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357534, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357534, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357535 q = 1) : d309673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357535, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357535, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357536 q = 1) : d309674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357536, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357536, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357537 q = 1) : d309675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357537, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357537, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357538 q = 1) : d309676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357538, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357538, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103646 (p : Pattern) (ha : d306035 p = 1) (hb : d357544 p = 1) : d309682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43970 q = 1) (hb : d306035 q = 1) : d309194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43970, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103231 q ha hb
    | true =>
      simp only [d43970, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103234 q ha hb
  have h2 (q : Pattern) (ha : d43971 q = 1) (hb : d306035 q = 1) : d309195 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43971, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43971, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357525 q = 1) : d309663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357525, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d357525, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357526 q = 1) : d309664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357526, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357526, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357528 q = 1) : d309666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357528, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357528, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103644 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357529 q = 1) : d309667 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357529, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357529, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357530 q = 1) : d309668 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357530, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357530, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d306035 q = 1) (hb : d357531 q = 1) : d309669 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357531, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357531, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d306035 q = 1) (hb : d357532 q = 1) : d309670 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357532, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357532, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306035 q = 1) (hb : d357539 q = 1) : d309677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357539, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357539, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103645 q ha hb
  have h11 (q : Pattern) (ha : d306035 q = 1) (hb : d357540 q = 1) : d309678 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357540, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357540, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d306035 q = 1) (hb : d357541 q = 1) : d309679 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357541, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357541, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d306035 q = 1) (hb : d357542 q = 1) : d309680 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357542, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357542, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d306035 q = 1) (hb : d357543 q = 1) : d309681 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357543, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357543, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d306035 q = 1) (hb : d357544 q = 1) : d309682 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357544, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357544, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro103647 (p : Pattern) (ha : d306035 p = 1) (hb : d357550 p = 1) : d309688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357545 q = 1) : d309683 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357545, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357545, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103646 q ha hb
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357546 q = 1) : d309684 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357546, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357546, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357547 q = 1) : d309685 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357547, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357547, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357548 q = 1) : d309686 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357548, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357548, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357549 q = 1) : d309687 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357549, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357549, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357550 q = 1) : d309688 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357550, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357550, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103648 (p : Pattern) (ha : d306035 p = 1) (hb : d357556 p = 1) : d309724 p = 1 := by
  have h0 (q : Pattern) (ha : d306035 q = 1) (hb : d357467 q = 1) : d309605 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103631 q ha hb
    | true =>
      simp only [d357467, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103635 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357494 q = 1) : d309632 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357494, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357494, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103639 q ha hb
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357495 q = 1) : d309633 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d357495, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357522 q = 1) : d309660 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357522, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357522, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103643 q ha hb
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357523 q = 1) : d309661 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357523, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357523, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357524 q = 1) : d309662 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306035 q = 1) (hb : d357551 q = 1) : d309689 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357551, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357551, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103647 q ha hb
  have h8 (q : Pattern) (ha : d306035 q = 1) (hb : d357552 q = 1) : d309690 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357552, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357552, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306035 q = 1) (hb : d357553 q = 1) : d309691 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357553, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357553, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306035 q = 1) (hb : d357554 q = 1) : d309692 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357554, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d306035 q = 1) (hb : d309722 q = 1) : d309722 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d306035 q = 1) (hb : d357555 q = 1) : d309723 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357555, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306035 q = 1) (hb : d357556 q = 1) : d309724 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357556, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro103649 (p : Pattern) (ha : d306035 p = 1) (hb : d357562 p = 1) : d309730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357557 q = 1) : d309725 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103648 q ha hb
    | true =>
      simp only [d357557, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357558 q = 1) : d309726 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357559 q = 1) : d309727 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357560 q = 1) : d309728 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357561 q = 1) : d309729 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357562 q = 1) : d309730 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103650 (p : Pattern) (ha : d306035 p = 1) (hb : d357568 p = 1) : d309736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357563 q = 1) : d309731 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103649 q ha hb
    | true =>
      simp only [d357563, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357564 q = 1) : d309732 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357565 q = 1) : d309733 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357566 q = 1) : d309734 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357567 q = 1) : d309735 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357568 q = 1) : d309736 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103651 (p : Pattern) (ha : d306035 p = 1) (hb : d357574 p = 1) : d309742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357569 q = 1) : d309737 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103650 q ha hb
    | true =>
      simp only [d357569, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357570 q = 1) : d309738 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357571 q = 1) : d309739 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357572 q = 1) : d309740 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357573 q = 1) : d309741 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357574 q = 1) : d309742 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103652 (p : Pattern) (ha : d306035 p = 1) (hb : d357580 p = 1) : d309748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357575 q = 1) : d309743 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103651 q ha hb
    | true =>
      simp only [d357575, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357576 q = 1) : d309744 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357577 q = 1) : d309745 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357578 q = 1) : d309746 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357579 q = 1) : d309747 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357580 q = 1) : d309748 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103653 (p : Pattern) (ha : d306035 p = 1) (hb : d357586 p = 1) : d309754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357581 q = 1) : d309749 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103652 q ha hb
    | true =>
      simp only [d357581, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357582 q = 1) : d309750 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357583 q = 1) : d309751 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357584 q = 1) : d309752 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357585 q = 1) : d309753 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357586 q = 1) : d309754 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103654 (p : Pattern) (ha : d306035 p = 1) (hb : d357592 p = 1) : d309760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357587 q = 1) : d309755 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103653 q ha hb
    | true =>
      simp only [d357587, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357588 q = 1) : d309756 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357589 q = 1) : d309757 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357590 q = 1) : d309758 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357591 q = 1) : d309759 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357592 q = 1) : d309760 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103655 (p : Pattern) (ha : d306035 p = 1) (hb : d357598 p = 1) : d309766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306035 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306035 q = 1) (hb : d357593 q = 1) : d309761 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103654 q ha hb
    | true =>
      simp only [d357593, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d306035 q = 1) (hb : d357594 q = 1) : d309762 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306035 q = 1) (hb : d357595 q = 1) : d309763 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d306035 q = 1) (hb : d357596 q = 1) : d309764 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306035 q = 1) (hb : d357597 q = 1) : d309765 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d306035 q = 1) (hb : d357598 q = 1) : d309766 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103656 (p : Pattern) (ha : d241986 p = 1) (hb : d308063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d241855 q = 1) (hb : d307999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d307999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103296 q ha hb
    | true =>
      simp only [d241855, d307999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d241976 q = 1) (hb : d308059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d241976, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d241983 q = 1) (hb : d308060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241983, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d241984 q = 1) (hb : d308061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241984, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241985 q = 1) (hb : d308062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241985, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241986 q = 1) (hb : d308063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d241986, d308063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241986, d308063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103657 (p : Pattern) (ha : d242005 p = 1) (hb : d308070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d241855 q = 1) (hb : d307999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d307999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103296 q ha hb
    | true =>
      simp only [d241855, d307999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d241976 q = 1) (hb : d308059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241976, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d241983 q = 1) (hb : d308060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241983, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d241984 q = 1) (hb : d308061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241984, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241985 q = 1) (hb : d308062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241985, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241991 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d241862 q = 1) (hb : d308006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d308006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103298 q ha hb
    | true =>
      simp only [d241862, d308006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d241998 q = 1) (hb : d308066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d241998, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242002 q = 1) (hb : d308067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242002, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242003 q = 1) (hb : d308068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242003, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242003, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242004 q = 1) (hb : d308069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242004, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242004, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242005 q = 1) (hb : d308070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242005, d308070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242005, d308070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103658 (p : Pattern) (ha : d242014 p = 1) (hb : d309556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241862 q = 1) (hb : d308006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d308006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103298 q ha hb
    | true =>
      simp only [d241862, d308006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d241998 q = 1) (hb : d308066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241998, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242002 q = 1) (hb : d308067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242002, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242012 q = 1) (hb : d308068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242012, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242012, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242013 q = 1) (hb : d308069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242013, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242013, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242014 q = 1) (hb : d309556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242014, d309556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242014, d309556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103659 (p : Pattern) (ha : d242054 p = 1) (hb : d309566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241898 q = 1) (hb : d308042 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241898, d308042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103303 q ha hb
    | true =>
      simp only [d241898, d308042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d242044 q = 1) (hb : d309562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242044, d309562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242044, d309562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242050 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242051 q = 1) (hb : d309563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242051, d309563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242051, d309563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242052 q = 1) (hb : d309564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242052, d309564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242052, d309564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242053 q = 1) (hb : d309565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242053, d309565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242053, d309565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242054 q = 1) (hb : d309566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242054, d309566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242054, d309566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103660 (p : Pattern) (ha : d242060 p = 1) (hb : d309572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242006 q = 1) (hb : d308071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242006, d308071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103656 q ha hb
    | true =>
      simp only [d242006, d308071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103657 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242009 q = 1) (hb : d308072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242009, d308072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242009, d308072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242010 q = 1) (hb : d309554 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242010, d309554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242010, d309554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242011 q = 1) (hb : d309555 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242011, d309555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242011, d309555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242015 q = 1) (hb : d309557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242015, d309557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242015, d309557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103658 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242016 q = 1) (hb : d309558 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242016, d309558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242016, d309558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242017 q = 1) (hb : d309559 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242017, d309559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242017, d309559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242018 q = 1) (hb : d309560 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242018, d309560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242018, d309560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242019 q = 1) (hb : d309561 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242019, d309561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242019, d309561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242055 q = 1) (hb : d309567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242055, d309567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242055, d309567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103659 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242056 q = 1) (hb : d309568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242056, d309568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242056, d309568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242057 q = 1) (hb : d309569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242057, d309569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242057, d309569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242058 q = 1) (hb : d309570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242058, d309570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242058, d309570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242059 q = 1) (hb : d309571 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242059, d309571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242059, d309571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242060 q = 1) (hb : d309572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242060, d309572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242060, d309572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103661 (p : Pattern) (ha : d242066 p = 1) (hb : d309578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d241910 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61294 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d241911 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d241912 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d241913 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d241914 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242061 q = 1) (hb : d309573 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242061, d309573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242061, d309573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103660 q ha hb
  have h8 (q : Pattern) (ha : d242062 q = 1) (hb : d309574 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242062, d309574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242062, d309574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242063 q = 1) (hb : d309575 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242063, d309575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242063, d309575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242064 q = 1) (hb : d309576 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242064, d309576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242064, d309576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d242065 q = 1) (hb : d309577 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242065, d309577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242065, d309577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d242066 q = 1) (hb : d309578 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242066, d309578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d242066, d309578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro103662 (p : Pattern) (ha : d242177 p = 1) (hb : d308233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242084 q = 1) (hb : d308228 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d308228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103334 q ha hb
    | true =>
      simp only [d242084, d308228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103335 q ha hb
  have h5 (q : Pattern) (ha : d242167 q = 1) (hb : d308229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242167, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242174 q = 1) (hb : d308230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242174, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242175 q = 1) (hb : d308231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242175, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242176 q = 1) (hb : d308232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242176, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242177 q = 1) (hb : d308233 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242177, d308233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242177, d308233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103663 (p : Pattern) (ha : d242198 p = 1) (hb : d308243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242084 q = 1) (hb : d308228 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d308228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103334 q ha hb
    | true =>
      simp only [d242084, d308228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103335 q ha hb
  have h4 (q : Pattern) (ha : d242167 q = 1) (hb : d308229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242167, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242174 q = 1) (hb : d308230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242174, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242175 q = 1) (hb : d308231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242175, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242176 q = 1) (hb : d308232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242176, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242183 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242094 q = 1) (hb : d308238 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d308238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103337 q ha hb
    | true =>
      simp only [d242094, d308238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103338 q ha hb
  have h13 (q : Pattern) (ha : d242191 q = 1) (hb : d308239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242191, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242195 q = 1) (hb : d308240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242195, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242196 q = 1) (hb : d308241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242196, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242196, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242197 q = 1) (hb : d308242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242197, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242197, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242198 q = 1) (hb : d308243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242198, d308243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242198, d308243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103664 (p : Pattern) (ha : d242218 p = 1) (hb : d309581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242094 q = 1) (hb : d308238 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d308238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103337 q ha hb
    | true =>
      simp only [d242094, d308238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103338 q ha hb
  have h3 (q : Pattern) (ha : d242191 q = 1) (hb : d308239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242191, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242195 q = 1) (hb : d308240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242195, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242216 q = 1) (hb : d308241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242216, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242216, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242217 q = 1) (hb : d308242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242217, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242217, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242218 q = 1) (hb : d309581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242218, d309581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242218, d309581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103665 (p : Pattern) (ha : d242286 p = 1) (hb : d309592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242275 q = 1) (hb : d309587 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242275, d309587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103372 q ha hb
    | true =>
      simp only [d242275, d309587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103375 q ha hb
  have h3 (q : Pattern) (ha : d242276 q = 1) (hb : d309588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242276, d309588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242276, d309588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242282 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242283 q = 1) (hb : d309589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242283, d309589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242283, d309589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242284 q = 1) (hb : d309590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242284, d309590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242284, d309590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242285 q = 1) (hb : d309591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242285, d309591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242285, d309591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242286 q = 1) (hb : d309592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242286, d309592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242286, d309592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103666 (p : Pattern) (ha : d242299 p = 1) (hb : d309598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242102 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242199 q = 1) (hb : d308244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242199, d308244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103662 q ha hb
    | true =>
      simp only [d242199, d308244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103663 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242212 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242213 q = 1) (hb : d308245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242213, d308245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242213, d308245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242214 q = 1) (hb : d309579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242214, d309579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242214, d309579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242215 q = 1) (hb : d309580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242215, d309580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242215, d309580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242219 q = 1) (hb : d309582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242219, d309582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242219, d309582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103664 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242221 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242222 q = 1) (hb : d309583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242222, d309583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242222, d309583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242223 q = 1) (hb : d309584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242223, d309584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242223, d309584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242224 q = 1) (hb : d309585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242224, d309585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242224, d309585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242225 q = 1) (hb : d309586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242225, d309586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242225, d309586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242287 q = 1) (hb : d309593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242287, d309593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242287, d309593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103665 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242294 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242295 q = 1) (hb : d309594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242295, d309594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242295, d309594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242296 q = 1) (hb : d309595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242296, d309595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242296, d309595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242297 q = 1) (hb : d309596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242297, d309596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242297, d309596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242298 q = 1) (hb : d309597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242298, d309597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242298, d309597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242299 q = 1) (hb : d309598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242299, d309598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242299, d309598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103667 (p : Pattern) (ha : d242305 p = 1) (hb : d309604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242300 q = 1) (hb : d309599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242300, d309599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242300, d309599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103666 q ha hb
  have h2 (q : Pattern) (ha : d242301 q = 1) (hb : d309600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242301, d309600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242301, d309600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242302 q = 1) (hb : d309601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242302, d309601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242302, d309601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242303 q = 1) (hb : d309602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242303, d309602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242303, d309602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242304 q = 1) (hb : d309603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242304, d309603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242304, d309603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242305 q = 1) (hb : d309604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242305, d309604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242305, d309604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103668 (p : Pattern) (ha : d242435 p = 1) (hb : d308491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242342 q = 1) (hb : d308486 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d308486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103385 q ha hb
    | true =>
      simp only [d242342, d308486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103386 q ha hb
  have h5 (q : Pattern) (ha : d242425 q = 1) (hb : d308487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242425, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242432 q = 1) (hb : d308488 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242432, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242433 q = 1) (hb : d308489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242433, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242434 q = 1) (hb : d308490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242434, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242435 q = 1) (hb : d308491 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242435, d308491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242435, d308491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103669 (p : Pattern) (ha : d242456 p = 1) (hb : d308501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242342 q = 1) (hb : d308486 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d308486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103385 q ha hb
    | true =>
      simp only [d242342, d308486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103386 q ha hb
  have h4 (q : Pattern) (ha : d242425 q = 1) (hb : d308487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242425, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242432 q = 1) (hb : d308488 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242432, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242433 q = 1) (hb : d308489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242433, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242434 q = 1) (hb : d308490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242434, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242352 q = 1) (hb : d308496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d308496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103388 q ha hb
    | true =>
      simp only [d242352, d308496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103389 q ha hb
  have h13 (q : Pattern) (ha : d242449 q = 1) (hb : d308497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242449, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242453 q = 1) (hb : d308498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242453, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242454 q = 1) (hb : d308499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242454, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242454, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242455 q = 1) (hb : d308500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242455, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242455, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242456 q = 1) (hb : d308501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242456, d308501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242456, d308501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103670 (p : Pattern) (ha : d242476 p = 1) (hb : d309608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242352 q = 1) (hb : d308496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d308496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103388 q ha hb
    | true =>
      simp only [d242352, d308496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103389 q ha hb
  have h3 (q : Pattern) (ha : d242449 q = 1) (hb : d308497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242449, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242453 q = 1) (hb : d308498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242453, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242474 q = 1) (hb : d308499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242474, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242474, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242475 q = 1) (hb : d308500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242475, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242475, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242476 q = 1) (hb : d309608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242476, d309608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242476, d309608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103671 (p : Pattern) (ha : d242561 p = 1) (hb : d309619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242550 q = 1) (hb : d309614 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242550, d309614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103426 q ha hb
    | true =>
      simp only [d242550, d309614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103429 q ha hb
  have h3 (q : Pattern) (ha : d242551 q = 1) (hb : d309615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242551, d309615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242551, d309615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242558 q = 1) (hb : d309616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242558, d309616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242558, d309616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242559 q = 1) (hb : d309617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242559, d309617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242559, d309617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242560 q = 1) (hb : d309618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242560, d309618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242560, d309618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242561 q = 1) (hb : d309619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242561, d309619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242561, d309619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103672 (p : Pattern) (ha : d242574 p = 1) (hb : d309625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242457 q = 1) (hb : d308502 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242457, d308502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103668 q ha hb
    | true =>
      simp only [d242457, d308502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103669 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242470 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242471 q = 1) (hb : d308503 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242471, d308503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242471, d308503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242472 q = 1) (hb : d309606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242472, d309606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242472, d309606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242473 q = 1) (hb : d309607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242473, d309607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242473, d309607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242477 q = 1) (hb : d309609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242477, d309609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242477, d309609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103670 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242479 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242480 q = 1) (hb : d309610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242480, d309610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242480, d309610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242481 q = 1) (hb : d309611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242481, d309611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242481, d309611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242482 q = 1) (hb : d309612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242482, d309612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242482, d309612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242483 q = 1) (hb : d309613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242483, d309613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242483, d309613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242562 q = 1) (hb : d309620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242562, d309620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242562, d309620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103671 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242569 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242570 q = 1) (hb : d309621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242570, d309621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242570, d309621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242571 q = 1) (hb : d309622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242571, d309622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242571, d309622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242572 q = 1) (hb : d309623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242572, d309623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242572, d309623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242573 q = 1) (hb : d309624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242573, d309624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242573, d309624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242574 q = 1) (hb : d309625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242574, d309625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242574, d309625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103673 (p : Pattern) (ha : d242580 p = 1) (hb : d309631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242575 q = 1) (hb : d309626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242575, d309626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242575, d309626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103672 q ha hb
  have h2 (q : Pattern) (ha : d242576 q = 1) (hb : d309627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242576, d309627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242576, d309627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242577 q = 1) (hb : d309628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242577, d309628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242577, d309628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242578 q = 1) (hb : d309629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242578, d309629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242578, d309629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242579 q = 1) (hb : d309630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242579, d309630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242579, d309630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242580 q = 1) (hb : d309631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242580, d309631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242580, d309631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103674 (p : Pattern) (ha : d242768 p = 1) (hb : d308813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242662 q = 1) (hb : d308808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d308808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103444 q ha hb
    | true =>
      simp only [d242662, d308808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103445 q ha hb
  have h5 (q : Pattern) (ha : d242749 q = 1) (hb : d308809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242749, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242765 q = 1) (hb : d308810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242765, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242766 q = 1) (hb : d308811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242766, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242767 q = 1) (hb : d308812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242767, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242768 q = 1) (hb : d308813 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242768, d308813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242768, d308813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103675 (p : Pattern) (ha : d242789 p = 1) (hb : d308823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242662 q = 1) (hb : d308808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d308808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103444 q ha hb
    | true =>
      simp only [d242662, d308808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103445 q ha hb
  have h4 (q : Pattern) (ha : d242749 q = 1) (hb : d308809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242749, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242765 q = 1) (hb : d308810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242765, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242766 q = 1) (hb : d308811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242766, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242767 q = 1) (hb : d308812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242767, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242672 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103447 q ha hb
    | true =>
      simp only [d242672, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103448 q ha hb
  have h13 (q : Pattern) (ha : d242782 q = 1) (hb : d308819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242782, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242786 q = 1) (hb : d308820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242786, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242787 q = 1) (hb : d308821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242787, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242787, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242788 q = 1) (hb : d308822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242788, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242788, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242789 q = 1) (hb : d308823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242789, d308823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242789, d308823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103676 (p : Pattern) (ha : d242809 p = 1) (hb : d309636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242672 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103447 q ha hb
    | true =>
      simp only [d242672, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103448 q ha hb
  have h3 (q : Pattern) (ha : d242782 q = 1) (hb : d308819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242782, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242786 q = 1) (hb : d308820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242786, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242807 q = 1) (hb : d308821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242807, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242807, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242808 q = 1) (hb : d308822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242808, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242808, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242809 q = 1) (hb : d309636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242809, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242809, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103677 (p : Pattern) (ha : d242930 p = 1) (hb : d309647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242910 q = 1) (hb : d309642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242910, d309642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103486 q ha hb
    | true =>
      simp only [d242910, d309642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103491 q ha hb
  have h3 (q : Pattern) (ha : d242911 q = 1) (hb : d309643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242911, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242911, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242927 q = 1) (hb : d309644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242927, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242927, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242928 q = 1) (hb : d309645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242928, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242928, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242929 q = 1) (hb : d309646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242929, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242929, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242930 q = 1) (hb : d309647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242930, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242930, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103678 (p : Pattern) (ha : d242943 p = 1) (hb : d309653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242790 q = 1) (hb : d308824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242790, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103674 q ha hb
    | true =>
      simp only [d242790, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103675 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242803 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242804 q = 1) (hb : d308825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242804, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242804, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242805 q = 1) (hb : d309634 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242805, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242805, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242806 q = 1) (hb : d309635 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242806, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242806, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242810 q = 1) (hb : d309637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242810, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242810, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103676 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242812 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242813 q = 1) (hb : d309638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242813, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242813, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242814 q = 1) (hb : d309639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242814, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242814, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242815 q = 1) (hb : d309640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242815, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242815, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242816 q = 1) (hb : d309641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242816, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242816, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242931 q = 1) (hb : d309648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242931, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242931, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103677 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242938 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242939 q = 1) (hb : d309649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242939, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242939, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242940 q = 1) (hb : d309650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242940, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242940, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242941 q = 1) (hb : d309651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242941, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242941, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242942 q = 1) (hb : d309652 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242942, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242942, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242943 q = 1) (hb : d309653 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242943, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242943, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103679 (p : Pattern) (ha : d242949 p = 1) (hb : d309659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242944 q = 1) (hb : d309654 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242944, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242944, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103678 q ha hb
  have h2 (q : Pattern) (ha : d242945 q = 1) (hb : d309655 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242945, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242945, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242946 q = 1) (hb : d309656 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242946, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242946, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242947 q = 1) (hb : d309657 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242947, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242947, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242948 q = 1) (hb : d309658 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242948, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242948, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242949 q = 1) (hb : d309659 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242949, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242949, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103680 (p : Pattern) (ha : d243151 p = 1) (hb : d309183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243045 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103507 q ha hb
    | true =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103508 q ha hb
  have h5 (q : Pattern) (ha : d243119 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243119, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243148 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243148, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243149 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243149, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243150 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243150, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243151 q = 1) (hb : d309183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243151, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243151, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103681 (p : Pattern) (ha : d243172 p = 1) (hb : d309193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243045 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103507 q ha hb
    | true =>
      simp only [d243045, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103508 q ha hb
  have h4 (q : Pattern) (ha : d243119 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243119, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243148 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243148, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243149 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243149, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243150 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243150, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243157 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243162 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243055 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103510 q ha hb
    | true =>
      simp only [d243055, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103511 q ha hb
  have h13 (q : Pattern) (ha : d243165 q = 1) (hb : d309189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243165, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243169 q = 1) (hb : d309190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243169, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243170 q = 1) (hb : d309191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243170, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243170, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243171 q = 1) (hb : d309192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243171, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243171, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243172 q = 1) (hb : d309193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243172, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243172, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103682 (p : Pattern) (ha : d243192 p = 1) (hb : d309665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243055 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103510 q ha hb
    | true =>
      simp only [d243055, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103511 q ha hb
  have h3 (q : Pattern) (ha : d243165 q = 1) (hb : d309189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243165, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243169 q = 1) (hb : d309190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243169, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243190 q = 1) (hb : d309191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243190, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243190, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243191 q = 1) (hb : d309192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243191, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243191, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243192 q = 1) (hb : d309665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243192, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243192, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103683 (p : Pattern) (ha : d243320 p = 1) (hb : d309676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243289 q = 1) (hb : d309671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243289, d309671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103550 q ha hb
    | true =>
      simp only [d243289, d309671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103556 q ha hb
  have h3 (q : Pattern) (ha : d243290 q = 1) (hb : d309672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243290, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243290, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243316 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243317 q = 1) (hb : d309673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243317, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243317, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243318 q = 1) (hb : d309674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243318, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243318, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243319 q = 1) (hb : d309675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243319, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243319, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243320 q = 1) (hb : d309676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243320, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243320, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103684 (p : Pattern) (ha : d243333 p = 1) (hb : d309682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243173 q = 1) (hb : d309194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243173, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103680 q ha hb
    | true =>
      simp only [d243173, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103681 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243187 q = 1) (hb : d309195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243187, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243187, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243188 q = 1) (hb : d309663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243188, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243188, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243189 q = 1) (hb : d309664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243189, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243189, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243193 q = 1) (hb : d309666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243193, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243193, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103682 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243195 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243196 q = 1) (hb : d309667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243196, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243196, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243197 q = 1) (hb : d309668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243197, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243197, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243198 q = 1) (hb : d309669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243198, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243198, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243199 q = 1) (hb : d309670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243199, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243199, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243321 q = 1) (hb : d309677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243321, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243321, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103683 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243329 q = 1) (hb : d309678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243329, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243329, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243330 q = 1) (hb : d309679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243330, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243330, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243331 q = 1) (hb : d309680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243331, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243331, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243332 q = 1) (hb : d309681 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243332, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243332, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243333 q = 1) (hb : d309682 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243333, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243333, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103685 (p : Pattern) (ha : d243339 p = 1) (hb : d309688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243334 q = 1) (hb : d309683 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243334, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243334, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103684 q ha hb
  have h2 (q : Pattern) (ha : d243335 q = 1) (hb : d309684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243335, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243335, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243336 q = 1) (hb : d309685 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243336, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243336, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243337 q = 1) (hb : d309686 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243337, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243337, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243338 q = 1) (hb : d309687 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243338, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243338, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243339 q = 1) (hb : d309688 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243339, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243339, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103686 (p : Pattern) (ha : d44504 p = 1) (hb : d243516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44499 q = 1) (hb : d243423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103569 q ha hb
    | true =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103570 q ha hb
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d243478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d243478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d243478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d243513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d243513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d243513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d243514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d243514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d243514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d243515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d243515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d243515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d243516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d243516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d243516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103687 (p : Pattern) (ha : d44514 p = 1) (hb : d243537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44499 q = 1) (hb : d243423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103569 q ha hb
    | true =>
      simp only [d44499, d243423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103570 q ha hb
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d243478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d243478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d243478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d243513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d243513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d243513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d243514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d243514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d243514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d243515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d243515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d243515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243522 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243527 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d44509 q = 1) (hb : d243433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d243433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103572 q ha hb
    | true =>
      simp only [d44509, d243433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103573 q ha hb
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d243530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d243530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d243530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d243534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d243534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d243534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d243535 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d243535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d243535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d243536 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d243536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d243536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d243537 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d243537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d243537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103688 (p : Pattern) (ha : d243557 p = 1) (hb : d309695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44509 q = 1) (hb : d243433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d243433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103572 q ha hb
    | true =>
      simp only [d44509, d243433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103573 q ha hb
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d243530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d243530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d243530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d243534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d243534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d243534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d243555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d243555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d243555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d243556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d243556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d243556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243557 q = 1) (hb : d309695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243557, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243557, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro103689 (p : Pattern) (ha : d243667 p = 1) (hb : d309706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243636 q = 1) (hb : d309701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243636, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103612 q hb ha
    | true =>
      simp only [d243636, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103581 q hb ha
  have h3 (q : Pattern) (ha : d243637 q = 1) (hb : d309702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243637, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243637, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243664 q = 1) (hb : d309703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243664, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243664, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243665 q = 1) (hb : d309704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243665, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243665, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243666 q = 1) (hb : d309705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243666, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243666, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243667 q = 1) (hb : d309706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243667, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243667, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103690 (p : Pattern) (ha : d243680 p = 1) (hb : d309712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243441 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d243538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d243538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103686 q ha hb
    | true =>
      simp only [d44515, d243538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103687 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d243552 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d243552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d243552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243553 q = 1) (hb : d309693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243553, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243553, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243554 q = 1) (hb : d309694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243554, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243554, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243558 q = 1) (hb : d309696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243558, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243558, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103688 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243560 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243561 q = 1) (hb : d309697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243561, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243561, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243562 q = 1) (hb : d309698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243562, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243562, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243563 q = 1) (hb : d309699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243563, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243563, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243564 q = 1) (hb : d309700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243564, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243564, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243668 q = 1) (hb : d309707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243668, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243668, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103689 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243676 q = 1) (hb : d309708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243676, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243676, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243677 q = 1) (hb : d309709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243677, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243677, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243678 q = 1) (hb : d309710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243678, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243678, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243679 q = 1) (hb : d309711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243679, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243679, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243680 q = 1) (hb : d309712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243680, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243680, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103691 (p : Pattern) (ha : d243686 p = 1) (hb : d309718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243681 q = 1) (hb : d309713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243681, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243681, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103690 q ha hb
  have h2 (q : Pattern) (ha : d243682 q = 1) (hb : d309714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243682, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243682, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243683 q = 1) (hb : d309715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243683, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243683, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243684 q = 1) (hb : d309716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243684, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243684, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243685 q = 1) (hb : d309717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243685, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243685, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243686 q = 1) (hb : d309718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243686, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243686, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103692 (p : Pattern) (ha : d243692 p = 1) (hb : d309724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d309605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103661 q ha hb
    | true =>
      simp only [d242306, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103667 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d309632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103673 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d309633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d309660 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103679 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d309661 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d309662 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d309689 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103685 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d309690 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d309691 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d309692 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103691 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d309723 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d309724 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro103693 (p : Pattern) (ha : d243698 p = 1) (hb : d309730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d309725 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103692 q ha hb
    | true =>
      simp only [d243693, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d309726 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d309727 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d309728 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d309729 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d309730 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103694 (p : Pattern) (ha : d243704 p = 1) (hb : d309736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d309731 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103693 q ha hb
    | true =>
      simp only [d243699, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d309732 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d309733 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d309734 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d309735 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d309736 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103695 (p : Pattern) (ha : d243710 p = 1) (hb : d309742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d309737 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103694 q ha hb
    | true =>
      simp only [d243705, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d309738 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d309739 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d309740 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d309741 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d309742 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103696 (p : Pattern) (ha : d243716 p = 1) (hb : d309748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d309743 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103695 q ha hb
    | true =>
      simp only [d243711, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d309744 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d309745 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d309746 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d309747 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d309748 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103697 (p : Pattern) (ha : d243722 p = 1) (hb : d309754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d309749 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103696 q ha hb
    | true =>
      simp only [d243717, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d309750 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d309751 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d309752 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d309753 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d309754 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103698 (p : Pattern) (ha : d243728 p = 1) (hb : d309760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d309755 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103697 q ha hb
    | true =>
      simp only [d243723, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d309756 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d309757 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d309758 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d309759 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d309760 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103699 (p : Pattern) (ha : d243734 p = 1) (hb : d309766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d309761 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103698 q ha hb
    | true =>
      simp only [d243729, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d309762 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d309763 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d309764 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d309765 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d309766 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro103700 (p : Pattern) (ha : d245392 p = 1) (hb : d308063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307999 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245388 q = 1) (hb : d308059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245388, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245389 q = 1) (hb : d308060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245389, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245390 q = 1) (hb : d308061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245390, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245391 q = 1) (hb : d308062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245391, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245392 q = 1) (hb : d308063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245392, d308063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245392, d308063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103701 (p : Pattern) (ha : d245397 p = 1) (hb : d308070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245388 q = 1) (hb : d308059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245388, d308059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245389 q = 1) (hb : d308060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245389, d308060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245390 q = 1) (hb : d308061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245390, d308061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245391 q = 1) (hb : d308062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245391, d308062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30816 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30820 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308006 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245393 q = 1) (hb : d308066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245393, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245394 q = 1) (hb : d308067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245394, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245395 q = 1) (hb : d308068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245395, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245395, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245396 q = 1) (hb : d308069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245396, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245396, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245397 q = 1) (hb : d308070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245397, d308070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245397, d308070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103702 (p : Pattern) (ha : d245404 p = 1) (hb : d309556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308006 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245393 q = 1) (hb : d308066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245393, d308066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245394 q = 1) (hb : d308067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245394, d308067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245402 q = 1) (hb : d308068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245402, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245402, d308068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245403 q = 1) (hb : d308069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245403, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245403, d308069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245404 q = 1) (hb : d309556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245404, d309556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245404, d309556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103703 (p : Pattern) (ha : d245414 p = 1) (hb : d309566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30870 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245410 q = 1) (hb : d309562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245410, d309562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245410, d309562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245411 q = 1) (hb : d309563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245411, d309563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245411, d309563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245412 q = 1) (hb : d309564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245412, d309564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245412, d309564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245413 q = 1) (hb : d309565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245413, d309565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245413, d309565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245414 q = 1) (hb : d309566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245414, d309566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245414, d309566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103704 (p : Pattern) (ha : d245420 p = 1) (hb : d309572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245398 q = 1) (hb : d308071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245398, d308071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103700 q ha hb
    | true =>
      simp only [d245398, d308071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103701 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245399 q = 1) (hb : d308072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245399, d308072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245399, d308072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245400 q = 1) (hb : d309554 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245400, d309554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245400, d309554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245401 q = 1) (hb : d309555 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245401, d309555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245401, d309555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245405 q = 1) (hb : d309557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245405, d309557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245405, d309557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103702 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245406 q = 1) (hb : d309558 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245406, d309558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245406, d309558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245407 q = 1) (hb : d309559 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245407, d309559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245407, d309559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245408 q = 1) (hb : d309560 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245408, d309560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245408, d309560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245409 q = 1) (hb : d309561 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245409, d309561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245409, d309561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245415 q = 1) (hb : d309567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245415, d309567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245415, d309567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103703 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245416 q = 1) (hb : d309568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245416, d309568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245416, d309568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245417 q = 1) (hb : d309569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245417, d309569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245417, d309569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245418 q = 1) (hb : d309570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245418, d309570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245418, d309570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245419 q = 1) (hb : d309571 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245419, d309571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245419, d309571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245420 q = 1) (hb : d309572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245420, d309572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245420, d309572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103705 (p : Pattern) (ha : d245426 p = 1) (hb : d309578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d245383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61343 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d245384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d245385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d245386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d245387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245421 q = 1) (hb : d309573 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245421, d309573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245421, d309573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103704 q ha hb
  have h8 (q : Pattern) (ha : d245422 q = 1) (hb : d309574 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245422, d309574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245422, d309574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245423 q = 1) (hb : d309575 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245423, d309575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245423, d309575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245424 q = 1) (hb : d309576 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245424, d309576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245424, d309576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245425 q = 1) (hb : d309577 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245425, d309577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245425, d309577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245426 q = 1) (hb : d309578 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245426, d309578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d245426, d309578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro103706 (p : Pattern) (ha : d245431 p = 1) (hb : d308233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d308228 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245427 q = 1) (hb : d308229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245427, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245428 q = 1) (hb : d308230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245428, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245429 q = 1) (hb : d308231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245429, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245430 q = 1) (hb : d308232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245430, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245431 q = 1) (hb : d308233 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245431, d308233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245431, d308233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103707 (p : Pattern) (ha : d245436 p = 1) (hb : d308243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308228 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245427 q = 1) (hb : d308229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245427, d308229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245428 q = 1) (hb : d308230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245428, d308230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245429 q = 1) (hb : d308231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245429, d308231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245430 q = 1) (hb : d308232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245430, d308232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31072 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308238 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245432 q = 1) (hb : d308239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245432, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245433 q = 1) (hb : d308240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245433, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245434 q = 1) (hb : d308241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245434, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245434, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245435 q = 1) (hb : d308242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245435, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245435, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245436 q = 1) (hb : d308243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245436, d308243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245436, d308243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103708 (p : Pattern) (ha : d245443 p = 1) (hb : d309581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308238 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245432 q = 1) (hb : d308239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245432, d308239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245433 q = 1) (hb : d308240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245433, d308240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245441 q = 1) (hb : d308241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245441, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245441, d308241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245442 q = 1) (hb : d308242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245442, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245442, d308242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245443 q = 1) (hb : d309581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245443, d309581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245443, d309581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103709 (p : Pattern) (ha : d245453 p = 1) (hb : d309592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245449 q = 1) (hb : d309588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245449, d309588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245449, d309588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31202 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245450 q = 1) (hb : d309589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245450, d309589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245450, d309589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245451 q = 1) (hb : d309590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245451, d309590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245451, d309590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245452 q = 1) (hb : d309591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245452, d309591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245452, d309591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245453 q = 1) (hb : d309592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245453, d309592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245453, d309592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103710 (p : Pattern) (ha : d245459 p = 1) (hb : d309598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245437 q = 1) (hb : d308244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245437, d308244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103706 q ha hb
    | true =>
      simp only [d245437, d308244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103707 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245438 q = 1) (hb : d308245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245438, d308245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245438, d308245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245439 q = 1) (hb : d309579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245439, d309579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245439, d309579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245440 q = 1) (hb : d309580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245440, d309580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245440, d309580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245444 q = 1) (hb : d309582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245444, d309582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245444, d309582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103708 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31113 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245445 q = 1) (hb : d309583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245445, d309583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245445, d309583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245446 q = 1) (hb : d309584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245446, d309584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245446, d309584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245447 q = 1) (hb : d309585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245447, d309585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245447, d309585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245448 q = 1) (hb : d309586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245448, d309586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245448, d309586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245454 q = 1) (hb : d309593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245454, d309593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245454, d309593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103709 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245455 q = 1) (hb : d309594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245455, d309594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245455, d309594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245456 q = 1) (hb : d309595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245456, d309595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245456, d309595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245457 q = 1) (hb : d309596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245457, d309596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245457, d309596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245458 q = 1) (hb : d309597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245458, d309597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245458, d309597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245459 q = 1) (hb : d309598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245459, d309598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245459, d309598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103711 (p : Pattern) (ha : d245465 p = 1) (hb : d309604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245460 q = 1) (hb : d309599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245460, d309599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245460, d309599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103710 q ha hb
  have h2 (q : Pattern) (ha : d245461 q = 1) (hb : d309600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245461, d309600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245461, d309600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245462 q = 1) (hb : d309601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245462, d309601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245462, d309601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245463 q = 1) (hb : d309602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245463, d309602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245463, d309602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245464 q = 1) (hb : d309603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245464, d309603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245464, d309603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245465 q = 1) (hb : d309604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245465, d309604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245465, d309604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103712 (p : Pattern) (ha : d245471 p = 1) (hb : d308491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d308486 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245467 q = 1) (hb : d308487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245467, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245468 q = 1) (hb : d308488 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245468, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245469 q = 1) (hb : d308489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245469, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245470 q = 1) (hb : d308490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245470, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245471 q = 1) (hb : d308491 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245471, d308491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245471, d308491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103713 (p : Pattern) (ha : d245476 p = 1) (hb : d308501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308486 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245467 q = 1) (hb : d308487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245467, d308487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245468 q = 1) (hb : d308488 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245468, d308488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245469 q = 1) (hb : d308489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245469, d308489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245470 q = 1) (hb : d308490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245470, d308490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308496 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245472 q = 1) (hb : d308497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245472, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245473 q = 1) (hb : d308498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245473, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245474 q = 1) (hb : d308499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245474, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245474, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245475 q = 1) (hb : d308500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245475, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245475, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245476 q = 1) (hb : d308501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245476, d308501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245476, d308501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103714 (p : Pattern) (ha : d245483 p = 1) (hb : d309608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245472 q = 1) (hb : d308497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245472, d308497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245473 q = 1) (hb : d308498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245473, d308498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245481 q = 1) (hb : d308499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245481, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245481, d308499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245482 q = 1) (hb : d308500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245482, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245482, d308500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245483 q = 1) (hb : d309608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245483, d309608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245483, d309608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103715 (p : Pattern) (ha : d245493 p = 1) (hb : d309619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245489 q = 1) (hb : d309615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245489, d309615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245489, d309615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31591 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245490 q = 1) (hb : d309616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245490, d309616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245490, d309616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245491 q = 1) (hb : d309617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245491, d309617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245491, d309617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245492 q = 1) (hb : d309618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245492, d309618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245492, d309618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245493 q = 1) (hb : d309619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245493, d309619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245493, d309619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103716 (p : Pattern) (ha : d245499 p = 1) (hb : d309625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245477 q = 1) (hb : d308502 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245477, d308502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103712 q ha hb
    | true =>
      simp only [d245477, d308502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103713 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31461 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245478 q = 1) (hb : d308503 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245478, d308503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245478, d308503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245479 q = 1) (hb : d309606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245479, d309606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245479, d309606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245480 q = 1) (hb : d309607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245480, d309607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245480, d309607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245484 q = 1) (hb : d309609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245484, d309609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245484, d309609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103714 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31470 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245485 q = 1) (hb : d309610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245485, d309610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245485, d309610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245486 q = 1) (hb : d309611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245486, d309611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245486, d309611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245487 q = 1) (hb : d309612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245487, d309612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245487, d309612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245488 q = 1) (hb : d309613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245488, d309613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245488, d309613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245494 q = 1) (hb : d309620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245494, d309620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245494, d309620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103715 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31607 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245495 q = 1) (hb : d309621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245495, d309621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245495, d309621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245496 q = 1) (hb : d309622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245496, d309622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245496, d309622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245497 q = 1) (hb : d309623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245497, d309623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245497, d309623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245498 q = 1) (hb : d309624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245498, d309624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245498, d309624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245499 q = 1) (hb : d309625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245499, d309625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245499, d309625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103717 (p : Pattern) (ha : d245505 p = 1) (hb : d309631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245500 q = 1) (hb : d309626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245500, d309626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245500, d309626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103716 q ha hb
  have h2 (q : Pattern) (ha : d245501 q = 1) (hb : d309627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245501, d309627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245501, d309627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245502 q = 1) (hb : d309628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245502, d309628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245502, d309628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245503 q = 1) (hb : d309629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245503, d309629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245503, d309629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245504 q = 1) (hb : d309630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245504, d309630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245504, d309630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245505 q = 1) (hb : d309631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245505, d309631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245505, d309631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103718 (p : Pattern) (ha : d245512 p = 1) (hb : d308813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d308808 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245508 q = 1) (hb : d308809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245508, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245509 q = 1) (hb : d308810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245509, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245510 q = 1) (hb : d308811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245510, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245511 q = 1) (hb : d308812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245511, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245512 q = 1) (hb : d308813 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d308813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245512, d308813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103719 (p : Pattern) (ha : d245517 p = 1) (hb : d308823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308808 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245508 q = 1) (hb : d308809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245508, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245509 q = 1) (hb : d308810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245509, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245510 q = 1) (hb : d308811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245510, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245511 q = 1) (hb : d308812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245511, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245513 q = 1) (hb : d308819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245513, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245514 q = 1) (hb : d308820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245514, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245515 q = 1) (hb : d308821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245515, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245516 q = 1) (hb : d308822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245516, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245517 q = 1) (hb : d308823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d308823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245517, d308823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103720 (p : Pattern) (ha : d245524 p = 1) (hb : d309636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245513 q = 1) (hb : d308819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245513, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245514 q = 1) (hb : d308820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245514, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245522 q = 1) (hb : d308821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245522, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245523 q = 1) (hb : d308822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245523, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245524 q = 1) (hb : d309636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245524, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103721 (p : Pattern) (ha : d245534 p = 1) (hb : d309647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245530 q = 1) (hb : d309643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245530, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245531 q = 1) (hb : d309644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245531, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245532 q = 1) (hb : d309645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245532, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245533 q = 1) (hb : d309646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245533, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245534 q = 1) (hb : d309647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245534, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103722 (p : Pattern) (ha : d245540 p = 1) (hb : d309653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31718 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245518 q = 1) (hb : d308824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103718 q ha hb
    | true =>
      simp only [d245518, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103719 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245519 q = 1) (hb : d308825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245519, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245520 q = 1) (hb : d309634 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245520, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245521 q = 1) (hb : d309635 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245521, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245525 q = 1) (hb : d309637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245525, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103720 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245526 q = 1) (hb : d309638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245526, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245527 q = 1) (hb : d309639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245527, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245528 q = 1) (hb : d309640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245528, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245529 q = 1) (hb : d309641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245529, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245535 q = 1) (hb : d309648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245535, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103721 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32125 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245536 q = 1) (hb : d309649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245536, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245537 q = 1) (hb : d309650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245537, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245538 q = 1) (hb : d309651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245538, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245539 q = 1) (hb : d309652 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245539, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245540 q = 1) (hb : d309653 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245540, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103723 (p : Pattern) (ha : d245546 p = 1) (hb : d309659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245541 q = 1) (hb : d309654 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245541, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103722 q ha hb
  have h2 (q : Pattern) (ha : d245542 q = 1) (hb : d309655 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245542, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245543 q = 1) (hb : d309656 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245543, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245544 q = 1) (hb : d309657 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245544, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245545 q = 1) (hb : d309658 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245545, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245546 q = 1) (hb : d309659 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245546, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103724 (p : Pattern) (ha : d245554 p = 1) (hb : d309183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245550 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245550, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245551 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245551, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245552 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245552, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245553 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245553, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245554 q = 1) (hb : d309183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245554, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245554, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103725 (p : Pattern) (ha : d245559 p = 1) (hb : d309193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245550 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245550, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245551 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245551, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245552 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245552, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245553 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245553, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245555 q = 1) (hb : d309189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245555, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245556 q = 1) (hb : d309190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245556, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245557 q = 1) (hb : d309191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245557, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245557, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245558 q = 1) (hb : d309192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245558, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245558, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245559 q = 1) (hb : d309193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245559, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245559, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103726 (p : Pattern) (ha : d245566 p = 1) (hb : d309665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245555 q = 1) (hb : d309189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245555, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245556 q = 1) (hb : d309190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245556, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245564 q = 1) (hb : d309191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245564, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245564, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245565 q = 1) (hb : d309192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245565, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245565, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245566 q = 1) (hb : d309665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245566, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245566, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103727 (p : Pattern) (ha : d245576 p = 1) (hb : d309676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309671 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245572 q = 1) (hb : d309672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245572, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245572, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245573 q = 1) (hb : d309673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245573, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245573, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245574 q = 1) (hb : d309674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245574, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245574, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245575 q = 1) (hb : d309675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245575, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245575, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245576 q = 1) (hb : d309676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245576, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245576, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103728 (p : Pattern) (ha : d245582 p = 1) (hb : d309682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245560 q = 1) (hb : d309194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245560, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103724 q ha hb
    | true =>
      simp only [d245560, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103725 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245561 q = 1) (hb : d309195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245561, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245561, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245562 q = 1) (hb : d309663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245562, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245562, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245563 q = 1) (hb : d309664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245563, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245563, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245567 q = 1) (hb : d309666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245567, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245567, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103726 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245568 q = 1) (hb : d309667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245568, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245568, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245569 q = 1) (hb : d309668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245569, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245569, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245570 q = 1) (hb : d309669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245570, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245570, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245571 q = 1) (hb : d309670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245571, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245571, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245577 q = 1) (hb : d309677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245577, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245577, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103727 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32671 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245578 q = 1) (hb : d309678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245578, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245578, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245579 q = 1) (hb : d309679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245579, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245579, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245580 q = 1) (hb : d309680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245580, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245580, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245581 q = 1) (hb : d309681 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245581, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245581, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245582 q = 1) (hb : d309682 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245582, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245582, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103729 (p : Pattern) (ha : d245588 p = 1) (hb : d309688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245583 q = 1) (hb : d309683 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245583, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245583, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103728 q ha hb
  have h2 (q : Pattern) (ha : d245584 q = 1) (hb : d309684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245584, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245584, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245585 q = 1) (hb : d309685 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245585, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245585, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245586 q = 1) (hb : d309686 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245586, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245586, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245587 q = 1) (hb : d309687 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245587, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245587, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245588 q = 1) (hb : d309688 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245588, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245588, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103730 (p : Pattern) (ha : d44504 p = 1) (hb : d245597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d245593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d245594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d245595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d245596 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d245597 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d245597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d245597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro103731 (p : Pattern) (ha : d44514 p = 1) (hb : d245602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d245593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d245594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d245595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d245596 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32950 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d245598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d245599 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d245600 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d245600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d245600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d245601 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d245601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d245601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d245602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d245602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d245602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro103732 (p : Pattern) (ha : d245609 p = 1) (hb : d309695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d245598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d245599 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d245607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d245607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d245607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d245608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d245608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d245608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245609 q = 1) (hb : d309695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245609, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245609, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro103733 (p : Pattern) (ha : d245619 p = 1) (hb : d309706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309701 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245615 q = 1) (hb : d309702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245615, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245615, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245616 q = 1) (hb : d309703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245616, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245616, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245617 q = 1) (hb : d309704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245617, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245617, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245618 q = 1) (hb : d309705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245618, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245618, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245619 q = 1) (hb : d309706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245619, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245619, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro103734 (p : Pattern) (ha : d245625 p = 1) (hb : d309712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d245603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d245603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103730 q ha hb
    | true =>
      simp only [d44515, d245603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103731 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d245604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d245604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d245604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245605 q = 1) (hb : d309693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245605, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245605, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245606 q = 1) (hb : d309694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245606, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245606, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245610 q = 1) (hb : d309696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245610, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245610, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103732 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245611 q = 1) (hb : d309697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245611, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245611, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245612 q = 1) (hb : d309698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245612, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245612, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245613 q = 1) (hb : d309699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245613, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245613, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245614 q = 1) (hb : d309700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245614, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245614, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245620 q = 1) (hb : d309707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245620, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245620, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103733 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245621 q = 1) (hb : d309708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245621, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245621, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245622 q = 1) (hb : d309709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245622, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245622, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245623 q = 1) (hb : d309710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245623, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245623, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245624 q = 1) (hb : d309711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245624, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245624, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245625 q = 1) (hb : d309712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245625, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245625, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro103735 (p : Pattern) (ha : d245631 p = 1) (hb : d309718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245626 q = 1) (hb : d309713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245626, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245626, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103734 q ha hb
  have h2 (q : Pattern) (ha : d245627 q = 1) (hb : d309714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245627, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245627, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245628 q = 1) (hb : d309715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245628, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245628, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245629 q = 1) (hb : d309716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245629, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245629, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245630 q = 1) (hb : d309717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245630, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245630, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245631 q = 1) (hb : d309718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245631, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245631, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro103736 (p : Pattern) (ha : d245637 p = 1) (hb : d309724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d245466 q = 1) (hb : d309605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245466, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103705 q ha hb
    | true =>
      simp only [d245466, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103711 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245506 q = 1) (hb : d309632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245506, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245506, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103717 q ha hb
  have h3 (q : Pattern) (ha : d245507 q = 1) (hb : d309633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245507, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245507, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245547 q = 1) (hb : d309660 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245547, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245547, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103723 q ha hb
  have h5 (q : Pattern) (ha : d245548 q = 1) (hb : d309661 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245548, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245548, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245549 q = 1) (hb : d309662 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245549, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245549, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245589 q = 1) (hb : d309689 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245589, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245589, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103729 q ha hb
  have h8 (q : Pattern) (ha : d245590 q = 1) (hb : d309690 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245590, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245590, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245591 q = 1) (hb : d309691 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245591, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245591, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245592 q = 1) (hb : d309692 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245592, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245592, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245632 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245632, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245632, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103735 q ha hb
  have h12 (q : Pattern) (ha : d245633 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245633, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245633, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245634 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245634, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245634, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245635 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245635, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245635, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245636 q = 1) (hb : d309723 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245636, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245636, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245637 q = 1) (hb : d309724 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245637, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245637, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro103737 (p : Pattern) (ha : d245643 p = 1) (hb : d309730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245638 q = 1) (hb : d309725 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245638, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103736 q ha hb
    | true =>
      simp only [d245638, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245639 q = 1) (hb : d309726 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245639, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245639, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245640 q = 1) (hb : d309727 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245640, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245640, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245641 q = 1) (hb : d309728 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245641, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245641, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245642 q = 1) (hb : d309729 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245642, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245642, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245643 q = 1) (hb : d309730 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245643, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245643, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103738 (p : Pattern) (ha : d245649 p = 1) (hb : d309736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245644 q = 1) (hb : d309731 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245644, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103737 q ha hb
    | true =>
      simp only [d245644, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245645 q = 1) (hb : d309732 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245645, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245645, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245646 q = 1) (hb : d309733 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245646, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245646, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245647 q = 1) (hb : d309734 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245647, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245647, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245648 q = 1) (hb : d309735 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245648, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245648, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245649 q = 1) (hb : d309736 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245649, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245649, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103739 (p : Pattern) (ha : d245655 p = 1) (hb : d309742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245650 q = 1) (hb : d309737 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245650, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103738 q ha hb
    | true =>
      simp only [d245650, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245651 q = 1) (hb : d309738 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245651, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245651, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245652 q = 1) (hb : d309739 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245652, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245652, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245653 q = 1) (hb : d309740 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245653, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245653, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245654 q = 1) (hb : d309741 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245654, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245654, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245655 q = 1) (hb : d309742 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245655, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245655, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103740 (p : Pattern) (ha : d245661 p = 1) (hb : d309748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245656 q = 1) (hb : d309743 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245656, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103739 q ha hb
    | true =>
      simp only [d245656, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245657 q = 1) (hb : d309744 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245657, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245657, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245658 q = 1) (hb : d309745 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245658, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245658, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245659 q = 1) (hb : d309746 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245659, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245659, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245660 q = 1) (hb : d309747 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245660, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245660, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245661 q = 1) (hb : d309748 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245661, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245661, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103741 (p : Pattern) (ha : d245667 p = 1) (hb : d309754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245662 q = 1) (hb : d309749 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245662, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103740 q ha hb
    | true =>
      simp only [d245662, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245663 q = 1) (hb : d309750 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245663, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245663, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245664 q = 1) (hb : d309751 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245664, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245664, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245665 q = 1) (hb : d309752 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245665, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245665, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245666 q = 1) (hb : d309753 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245666, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245666, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245667 q = 1) (hb : d309754 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245667, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245667, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103742 (p : Pattern) (ha : d245673 p = 1) (hb : d309760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245668 q = 1) (hb : d309755 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245668, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103741 q ha hb
    | true =>
      simp only [d245668, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245669 q = 1) (hb : d309756 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245669, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245669, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245670 q = 1) (hb : d309757 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245670, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245670, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245671 q = 1) (hb : d309758 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245671, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245671, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245672 q = 1) (hb : d309759 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245672, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245672, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245673 q = 1) (hb : d309760 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245673, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245673, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103743 (p : Pattern) (ha : d245679 p = 1) (hb : d309766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245674 q = 1) (hb : d309761 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245674, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103742 q ha hb
    | true =>
      simp only [d245674, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245675 q = 1) (hb : d309762 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245675, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245675, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245676 q = 1) (hb : d309763 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245676, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245676, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245677 q = 1) (hb : d309764 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245677, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245677, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245678 q = 1) (hb : d309765 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245678, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245678, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245679 q = 1) (hb : d309766 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245679, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245679, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro103744 (p : Pattern) (ha : d46460 p = 1) (hb : d325306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44996 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, d325306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44996, d325306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46459 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46460 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro103745 (p : Pattern) (ha : d46466 p = 1) (hb : d325306 p = 1) : d324616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103744 q ha hb
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d325306 q = 1) : d32155 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46462 q = 1) (hb : d325306 q = 1) : d324612 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46463 q = 1) (hb : d325306 q = 1) : d324613 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46464 q = 1) (hb : d325306 q = 1) : d324614 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46465 q = 1) (hb : d325306 q = 1) : d324615 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46466 q = 1) (hb : d325306 q = 1) : d324616 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46466, d324616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46466, d324616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro103746 (p : Pattern) (ha : d46473 p = 1) (hb : d325306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45587 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45587, d325306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45587, d325306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46472 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46473 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro103747 (p : Pattern) (ha : d46482 p = 1) (hb : d325306 p = 1) : d324622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103744 q ha hb
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d325306 q = 1) : d32155 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46462 q = 1) (hb : d325306 q = 1) : d324612 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, d324612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46463 q = 1) (hb : d325306 q = 1) : d324613 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, d324613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46464 q = 1) (hb : d325306 q = 1) : d324614 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, d324614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46465 q = 1) (hb : d325306 q = 1) : d324615 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, d324615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46474 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103746 q ha hb
  have h8 (q : Pattern) (ha : d1115 q = 1) (hb : d325306 q = 1) : d1115 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d46475 q = 1) (hb : d325306 q = 1) : d221076 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, d221076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46475, d221076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46476 q = 1) (hb : d325306 q = 1) : d221096 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, d221096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46476, d221096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46477 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103746 q ha hb
    | true =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19 q = 1) (hb : d325306 q = 1) : d19 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46478 q = 1) (hb : d325306 q = 1) : d221097 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, d221097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46478, d221097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46479 q = 1) (hb : d325306 q = 1) : d221098 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, d221098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46479, d221098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46480 q = 1) (hb : d325306 q = 1) : d221099 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, d221099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46480, d221099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46481 q = 1) (hb : d325306 q = 1) : d221100 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, d221100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46481, d221100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d46482 q = 1) (hb : d325306 q = 1) : d324622 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46482, d324622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46482, d324622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro103748 (p : Pattern) (ha : d46488 p = 1) (hb : d325306 p = 1) : d324628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d325306 q = 1) : d324617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103745 q ha hb
    | true =>
      simp only [d46467, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d325306 q = 1) : d324618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d325306 q = 1) : d324619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d325306 q = 1) : d324620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46471 q = 1) (hb : d325306 q = 1) : d324621 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, d324621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46471, d324621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46483 q = 1) (hb : d325306 q = 1) : d324623 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103747 q ha hb
    | true =>
      simp only [d46483, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46484 q = 1) (hb : d325306 q = 1) : d324624 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46484, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46485 q = 1) (hb : d325306 q = 1) : d324625 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46486 q = 1) (hb : d325306 q = 1) : d324626 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46486, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46487 q = 1) (hb : d325306 q = 1) : d324627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46488 q = 1) (hb : d325306 q = 1) : d324628 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46488, d324628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46488, d324628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro103749 (p : Pattern) (ha : d46490 p = 1) (hb : d325306 p = 1) : d324630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d325306 q = 1) : d324617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103745 q ha hb
    | true =>
      simp only [d46467, d324617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d325306 q = 1) : d324618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, d324618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d325306 q = 1) : d324619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, d324619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d325306 q = 1) : d324620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, d324620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46483 q = 1) (hb : d325306 q = 1) : d324623 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103747 q ha hb
    | true =>
      simp only [d46483, d324623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46484 q = 1) (hb : d325306 q = 1) : d324624 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46484, d324624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46485 q = 1) (hb : d325306 q = 1) : d324625 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, d324625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46486 q = 1) (hb : d325306 q = 1) : d324626 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46486, d324626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46487 q = 1) (hb : d325306 q = 1) : d324627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, d324627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46489 q = 1) (hb : d325306 q = 1) : d324629 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, d324629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46489, d324629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46490 q = 1) (hb : d325306 q = 1) : d324630 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46490, d324630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46490, d324630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
end NetHack.Soko22Hazard87
