import NetHack.Soko22Hazard87.AndIntroBlocks0236
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro59250 (p : Pattern) (ha : d199502 p = 1) (hb : d241012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199489 q = 1) (hb : d240999 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199489, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59247 q ha hb
    | true =>
      simp only [d199489, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199490 q = 1) (hb : d241000 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199490, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199490, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199497 q = 1) (hb : d241007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199497, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59249 q ha hb
    | true =>
      simp only [d199497, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199498 q = 1) (hb : d241008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199498, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199498, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199499 q = 1) (hb : d241009 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199499, d241009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199499, d241009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199500 q = 1) (hb : d241010 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199500, d241010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199500, d241010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199501 q = 1) (hb : d241011 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199501, d241011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199501, d241011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199502 q = 1) (hb : d241012 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199502, d241012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199502, d241012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59251 (p : Pattern) (ha : d199510 p = 1) (hb : d241015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199453 q = 1) (hb : d240972 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199453, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199453, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59201 q ha hb
  have h2 (q : Pattern) (ha : d199242 q = 1) (hb : d240809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199242, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59201 q ha hb
    | true =>
      simp only [d199242, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199454 q = 1) (hb : d240973 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199454, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199454, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199243 q = 1) (hb : d240810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199243, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199243, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199455 q = 1) (hb : d240974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199455, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199455, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199456 q = 1) (hb : d240975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199456, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199456, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199462 q = 1) (hb : d240981 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199462, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199462, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199510 q = 1) (hb : d241015 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199510, d241015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199510, d241015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59252 (p : Pattern) (ha : d199516 p = 1) (hb : d241021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199474 q = 1) (hb : d240983 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199474, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59242 q ha hb
    | true =>
      simp only [d199474, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59244 q ha hb
  have h2 (q : Pattern) (ha : d199475 q = 1) (hb : d240984 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199475, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199475, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199476 q = 1) (hb : d240985 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199476, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199476, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199478 q = 1) (hb : d240988 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199478, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59244 q ha hb
    | true =>
      simp only [d199478, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59245 q ha hb
  have h5 (q : Pattern) (ha : d199479 q = 1) (hb : d240989 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199479, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199479, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199480 q = 1) (hb : d240990 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199480, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199480, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199481 q = 1) (hb : d240991 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199481, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199481, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199511 q = 1) (hb : d241016 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199511, d241016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59244 q ha hb
    | true =>
      simp only [d199511, d241016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59251 q ha hb
  have h9 (q : Pattern) (ha : d199512 q = 1) (hb : d241017 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199512, d241017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199512, d241017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199513 q = 1) (hb : d241018 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199513, d241018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199513, d241018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199514 q = 1) (hb : d241019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199514, d241019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199514, d241019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199515 q = 1) (hb : d241020 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199515, d241020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199515, d241020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199516 q = 1) (hb : d241021 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199516, d241021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199516, d241021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro59253 (p : Pattern) (ha : d199522 p = 1) (hb : d241027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199517 q = 1) (hb : d241022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199517, d241022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59252 q ha hb
    | true =>
      simp only [d199517, d241022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199518 q = 1) (hb : d241023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199518, d241023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199518, d241023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199519 q = 1) (hb : d241024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199519, d241024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199519, d241024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199520 q = 1) (hb : d241025 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199520, d241025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199520, d241025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199521 q = 1) (hb : d241026 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199521, d241026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199521, d241026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199522 q = 1) (hb : d241027 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199522, d241027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199522, d241027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59254 (p : Pattern) (ha : d199528 p = 1) (hb : d241033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199503 q = 1) (hb : d241013 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199503, d241013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59248 q ha hb
    | true =>
      simp only [d199503, d241013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59250 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199508 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199509 q = 1) (hb : d241014 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199509, d241014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199509, d241014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d199523 q = 1) (hb : d241028 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199523, d241028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59253 q ha hb
    | true =>
      simp only [d199523, d241028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199524 q = 1) (hb : d241029 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199524, d241029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199524, d241029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199525 q = 1) (hb : d241030 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199525, d241030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199525, d241030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199526 q = 1) (hb : d241031 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199526, d241031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199526, d241031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199527 q = 1) (hb : d241032 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199527, d241032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199527, d241032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199528 q = 1) (hb : d241033 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199528, d241033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199528, d241033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro59255 (p : Pattern) (ha : d199507 p = 1) (hb : d241038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199497 q = 1) (hb : d241007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199497, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59249 q ha hb
    | true =>
      simp only [d199497, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199498 q = 1) (hb : d241008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199498, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199498, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199504 q = 1) (hb : d241035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199504, d241035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199504, d241035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199505 q = 1) (hb : d241036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199505, d241036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199505, d241036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199506 q = 1) (hb : d241037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199506, d241037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199506, d241037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199507 q = 1) (hb : d241038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199507, d241038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199507, d241038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59256 (p : Pattern) (ha : d199535 p = 1) (hb : d241044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199530 q = 1) (hb : d241039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199530, d241039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59255 q ha hb
    | true =>
      simp only [d199530, d241039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199531 q = 1) (hb : d241040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199531, d241040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199531, d241040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199532 q = 1) (hb : d241041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199532, d241041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199532, d241041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199533 q = 1) (hb : d241042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199533, d241042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199533, d241042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199534 q = 1) (hb : d241043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199534, d241043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199534, d241043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199535 q = 1) (hb : d241044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199535, d241044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199535, d241044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59257 (p : Pattern) (ha : d199541 p = 1) (hb : d241050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199289 q = 1) (hb : d240848 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199289, d240848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199289, d240848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59211 q ha hb
  have h2 (q : Pattern) (ha : d199290 q = 1) (hb : d240849 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199290, d240849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199290, d240849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199299 q = 1) (hb : d240858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199299, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59211 q ha hb
    | true =>
      simp only [d199299, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59214 q ha hb
  have h4 (q : Pattern) (ha : d199300 q = 1) (hb : d240859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199300, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199300, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199301 q = 1) (hb : d240860 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199301, d240860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199301, d240860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199398 q = 1) (hb : d240939 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199398, d240939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59229 q ha hb
    | true =>
      simp only [d199398, d240939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59236 q ha hb
  have h7 (q : Pattern) (ha : d199411 q = 1) (hb : d240952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199411, d240952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59237 q ha hb
    | true =>
      simp only [d199411, d240952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59238 q ha hb
  have h8 (q : Pattern) (ha : d199412 q = 1) (hb : d240953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199412, d240953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199412, d240953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199413 q = 1) (hb : d240954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199413, d240954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199413, d240954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d199414 q = 1) (hb : d240955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199414, d240955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199414, d240955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199418 q = 1) (hb : d240959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199418, d240959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199418, d240959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59239 q ha hb
  have h12 (q : Pattern) (ha : d199420 q = 1) (hb : d240961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199420, d240961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199420, d240961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59240 q ha hb
  have h13 (q : Pattern) (ha : d199421 q = 1) (hb : d240962 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199421, d240962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d199421, d240962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199422 q = 1) (hb : d240963 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199422, d240963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199422, d240963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d199423 q = 1) (hb : d240964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199423, d240964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d199423, d240964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d199424 q = 1) (hb : d240965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199424, d240965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199424, d240965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199529 q = 1) (hb : d241034 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199529, d241034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199529, d241034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59254 q ha hb
  have h18 (q : Pattern) (ha : d199536 q = 1) (hb : d241045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199536, d241045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199536, d241045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59256 q ha hb
  have h19 (q : Pattern) (ha : d199537 q = 1) (hb : d241046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199537, d241046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199537, d241046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d199538 q = 1) (hb : d241047 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199538, d241047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d199538, d241047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d199539 q = 1) (hb : d241048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199539, d241048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d199539, d241048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d199540 q = 1) (hb : d241049 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199540, d241049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d199540, d241049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d199541 q = 1) (hb : d241050 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199541, d241050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199541, d241050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro59258 (p : Pattern) (ha : d199547 p = 1) (hb : d241056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199542 q = 1) (hb : d241051 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199542, d241051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199542, d241051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59257 q ha hb
  have h2 (q : Pattern) (ha : d199543 q = 1) (hb : d241052 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199543, d241052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199543, d241052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199544 q = 1) (hb : d241053 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199544, d241053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199544, d241053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199545 q = 1) (hb : d241054 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199545, d241054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199545, d241054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199546 q = 1) (hb : d241055 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199546, d241055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199546, d241055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199547 q = 1) (hb : d241056 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199547, d241056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199547, d241056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59259 (p : Pattern) (ha : d26567 p = 1) (hb : d199562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10051 q = 1) (hb : d101478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10052 q = 1) (hb : d199557 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d199557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10052, d199557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10053 q = 1) (hb : d199558 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d199558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10053, d199558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h9 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h10 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26558 q = 1) (hb : d199559 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d26559 q = 1) (hb : d199560 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26559, d199560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26559, d199560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d26560 q = 1) (hb : d199561 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26560, d199561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26560, d199561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d26567 q = 1) (hb : d199562 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26567, d199562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26567, d199562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro59260 (p : Pattern) (ha : d26567 p = 1) (hb : d199568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10051 q = 1) (hb : d101478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10052 q = 1) (hb : d101479 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10053 q = 1) (hb : d101480 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h8 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h9 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26558 q = 1) (hb : d199559 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d26559 q = 1) (hb : d199560 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26559, d199560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26559, d199560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d26560 q = 1) (hb : d199561 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26560, d199561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26560, d199561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d26567 q = 1) (hb : d199568 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26567, d199568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26567, d199568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro59261 (p : Pattern) (ha : d26658 p = 1) (hb : d199551 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d10042 q = 1) (hb : d101469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199319 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10043 q = 1) (hb : d199320 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d199320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10043, d199320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10044 q = 1) (hb : d199321 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d199321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10044, d199321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h8 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h9 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10051 q = 1) (hb : d101478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10052 q = 1) (hb : d101479 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10053 q = 1) (hb : d101480 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26658 q = 1) (hb : d199551 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26658, d199551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26658, d199551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro59262 (p : Pattern) (ha : d199575 p = 1) (hb : d241060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26558 q = 1) (hb : d199559 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101508 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26559 q = 1) (hb : d199573 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26559, d199573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26559, d199573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26560 q = 1) (hb : d199574 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26560, d199574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26560, d199574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h9 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h10 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1593 q = 1) (hb : d53034 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1594 q = 1) (hb : d101559 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1594, d101559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1594, d101559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1595 q = 1) (hb : d101560 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1595, d101560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1595, d101560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d199575 q = 1) (hb : d241060 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d199575, d241060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d199575, d241060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro59263 (p : Pattern) (ha : d199581 p = 1) (hb : d241066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26659 q = 1) (hb : d199552 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59261 q ha hb
    | true =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26660 q = 1) (hb : d199553 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26661 q = 1) (hb : d199554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26661, d199554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26661, d199554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26662 q = 1) (hb : d199555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26662, d199555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26662, d199555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26568 q = 1) (hb : d199563 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59259 q ha hb
    | true =>
      simp only [d26568, d199563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26569 q = 1) (hb : d199564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26569, d199564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26570 q = 1) (hb : d199565 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26570, d199565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26570, d199565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26571 q = 1) (hb : d199566 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26571, d199566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26571, d199566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26663 q = 1) (hb : d199567 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26663, d199567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26663, d199567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26568 q = 1) (hb : d199569 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
    | true =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26569 q = 1) (hb : d199570 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26570 q = 1) (hb : d199571 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26570, d199571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26570, d199571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26571 q = 1) (hb : d199572 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26571, d199572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26571, d199572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d199578 q = 1) (hb : d241063 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199579 q = 1) (hb : d241064 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d199580 q = 1) (hb : d241065 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199580, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d199580, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d199581 q = 1) (hb : d241066 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199581, d241066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199581, d241066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59264 (p : Pattern) (ha : d26567 p = 1) (hb : d199584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10051 q = 1) (hb : d101478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10052 q = 1) (hb : d199557 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d199557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10052, d199557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10053 q = 1) (hb : d199558 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d199558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10053, d199558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h9 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h10 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26558 q = 1) (hb : d199559 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d199015 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d26559 q = 1) (hb : d199582 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26559, d199582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26559, d199582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26560 q = 1) (hb : d199583 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26560, d199583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26560, d199583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d26567 q = 1) (hb : d199584 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26567, d199584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26567, d199584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59265 (p : Pattern) (ha : d199591 p = 1) (hb : d241068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26568 q = 1) (hb : d199585 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59264 q ha hb
    | true =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26569 q = 1) (hb : d199586 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26570 q = 1) (hb : d199587 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26570, d199587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26570, d199587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26571 q = 1) (hb : d199588 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26571, d199588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26571, d199588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199578 q = 1) (hb : d241063 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199579 q = 1) (hb : d241064 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199589 q = 1) (hb : d241065 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199589, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199589, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199590 q = 1) (hb : d241067 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199590, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199590, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199591 q = 1) (hb : d241068 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199591, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199591, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59266 (p : Pattern) (ha : d1596 p = 1) (hb : d101561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h3 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1593 q = 1) (hb : d53034 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1594 q = 1) (hb : d101559 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1594, d101559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1594, d101559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1595 q = 1) (hb : d101560 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1595, d101560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1595, d101560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1596 q = 1) (hb : d101561 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1596, d101561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1596, d101561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59267 (p : Pattern) (ha : d199595 p = 1) (hb : d241072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199578 q = 1) (hb : d241063 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199579 q = 1) (hb : d241064 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199590 q = 1) (hb : d241067 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199590, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199590, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d1597 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59266 q ha hb
    | true =>
      simp only [d1597, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1598 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1598, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1599 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1599, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1599, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1600 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1600, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1600, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1601 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1601, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1601, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d199595 q = 1) (hb : d241072 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199595, d241072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199595, d241072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro59268 (p : Pattern) (ha : d199602 p = 1) (hb : d241079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199592 q = 1) (hb : d241069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199592, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59263 q ha hb
    | true =>
      simp only [d199592, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59265 q ha hb
  have h2 (q : Pattern) (ha : d199593 q = 1) (hb : d241070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199593, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199593, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199594 q = 1) (hb : d241071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199594, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199594, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199596 q = 1) (hb : d241073 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59265 q ha hb
    | true =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59267 q ha hb
  have h5 (q : Pattern) (ha : d199597 q = 1) (hb : d241074 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199598 q = 1) (hb : d241075 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199599 q = 1) (hb : d241076 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199599, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199599, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199600 q = 1) (hb : d241077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199600, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199600, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199601 q = 1) (hb : d241078 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199601, d241078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199601, d241078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199602 q = 1) (hb : d241079 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199602, d241079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199602, d241079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro59269 (p : Pattern) (ha : d199606 p = 1) (hb : d241083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199596 q = 1) (hb : d241073 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59265 q ha hb
    | true =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59267 q ha hb
  have h2 (q : Pattern) (ha : d199597 q = 1) (hb : d241074 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199598 q = 1) (hb : d241075 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199600 q = 1) (hb : d241077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199600, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199600, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199605 q = 1) (hb : d241082 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199605, d241082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199605, d241082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199606 q = 1) (hb : d241083 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199606, d241083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199606, d241083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59270 (p : Pattern) (ha : d199612 p = 1) (hb : d241089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199609 q = 1) (hb : d241086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199610 q = 1) (hb : d241087 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199611 q = 1) (hb : d241088 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199611, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199611, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199612 q = 1) (hb : d241089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199612, d241089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199612, d241089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59271 (p : Pattern) (ha : d199616 p = 1) (hb : d241093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199613 q = 1) (hb : d241090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199614 q = 1) (hb : d241091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199615 q = 1) (hb : d241092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199615, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199615, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199616 q = 1) (hb : d241093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199616, d241093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199616, d241093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59272 (p : Pattern) (ha : d199622 p = 1) (hb : d241099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199617 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59270 q ha hb
    | true =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59271 q ha hb
  have h2 (q : Pattern) (ha : d199618 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199618, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199618, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199619 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199619, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199619, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199620 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199620, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199620, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199621 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199621, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199621, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199622 q = 1) (hb : d241099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199622, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199622, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59273 (p : Pattern) (ha : d199625 p = 1) (hb : d241102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199609 q = 1) (hb : d241086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199610 q = 1) (hb : d241087 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199611 q = 1) (hb : d241088 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199611, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199611, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199625 q = 1) (hb : d241102 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199625, d241102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199625, d241102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59274 (p : Pattern) (ha : d199626 p = 1) (hb : d241103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199613 q = 1) (hb : d241090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199614 q = 1) (hb : d241091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199615 q = 1) (hb : d241092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199615, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199615, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199626 q = 1) (hb : d241103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199626, d241103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199626, d241103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59275 (p : Pattern) (ha : d199632 p = 1) (hb : d241109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199617 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59270 q ha hb
    | true =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59271 q ha hb
  have h2 (q : Pattern) (ha : d199618 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199618, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199618, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199619 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199619, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199619, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199620 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199620, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199620, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199621 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199621, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199621, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199627 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59273 q ha hb
    | true =>
      simp only [d199627, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59274 q ha hb
  have h7 (q : Pattern) (ha : d199628 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199628, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199628, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199629 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199629, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199629, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199630 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199630, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199630, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199631 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199631, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199631, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199632 q = 1) (hb : d241109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199632, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199632, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59276 (p : Pattern) (ha : d199637 p = 1) (hb : d241114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199609 q = 1) (hb : d241086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199610 q = 1) (hb : d241087 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199636 q = 1) (hb : d241113 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199636, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199636, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199637 q = 1) (hb : d241114 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199637, d241114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199637, d241114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59277 (p : Pattern) (ha : d199639 p = 1) (hb : d241116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199613 q = 1) (hb : d241090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199614 q = 1) (hb : d241091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199638 q = 1) (hb : d241115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199638, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199638, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199639 q = 1) (hb : d241116 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199639, d241116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199639, d241116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59278 (p : Pattern) (ha : d199646 p = 1) (hb : d241123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199609 q = 1) (hb : d241086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199644 q = 1) (hb : d241121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199644, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199644, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199645 q = 1) (hb : d241122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199645, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199645, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199646 q = 1) (hb : d241123 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199646, d241123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199646, d241123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59279 (p : Pattern) (ha : d199649 p = 1) (hb : d241126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199613 q = 1) (hb : d241090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199647 q = 1) (hb : d241124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199647, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199647, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199648 q = 1) (hb : d241125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199648, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199648, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199649 q = 1) (hb : d241126 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199649, d241126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199649, d241126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59280 (p : Pattern) (ha : d26652 p = 1) (hb : d199653 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d10042 q = 1) (hb : d101469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10043 q = 1) (hb : d101470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10044 q = 1) (hb : d101471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26652 q = 1) (hb : d199653 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26652, d199653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26652, d199653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59281 (p : Pattern) (ha : d26658 p = 1) (hb : d199659 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d10042 q = 1) (hb : d101469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10043 q = 1) (hb : d101470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10044 q = 1) (hb : d101471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d10051 q = 1) (hb : d101478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10052 q = 1) (hb : d101479 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10053 q = 1) (hb : d101480 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26658 q = 1) (hb : d199659 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26658, d199659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26658, d199659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro59282 (p : Pattern) (ha : d199665 p = 1) (hb : d241131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26653 q = 1) (hb : d199654 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26653, d199654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59280 q ha hb
    | true =>
      simp only [d26653, d199654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26654 q = 1) (hb : d199655 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26654, d199655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26654, d199655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26655 q = 1) (hb : d199656 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26655, d199656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26655, d199656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26656 q = 1) (hb : d199657 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26656, d199657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26656, d199657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26659 q = 1) (hb : d199552 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59261 q ha hb
    | true =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26660 q = 1) (hb : d199553 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26661 q = 1) (hb : d199554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26661, d199554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26661, d199554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26662 q = 1) (hb : d199555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26662, d199555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26662, d199555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d199658 q = 1) (hb : d241130 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199658, d241130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199658, d241130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d26659 q = 1) (hb : d199660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26659, d199660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59281 q ha hb
    | true =>
      simp only [d26659, d199660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26660 q = 1) (hb : d199661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26660, d199661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26660, d199661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26661 q = 1) (hb : d199662 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26661, d199662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26661, d199662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26662 q = 1) (hb : d199663 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26662, d199663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26662, d199663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d26568 q = 1) (hb : d199569 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
    | true =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26569 q = 1) (hb : d199570 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d26570 q = 1) (hb : d199571 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26570, d199571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26570, d199571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26571 q = 1) (hb : d199572 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26571, d199572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26571, d199572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26663 q = 1) (hb : d199664 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26663, d199664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26663, d199664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d199665 q = 1) (hb : d241131 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199665, d241131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199665, d241131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro59283 (p : Pattern) (ha : d199669 p = 1) (hb : d241068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26568 q = 1) (hb : d199569 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
    | true =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26569 q = 1) (hb : d199570 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26570 q = 1) (hb : d199571 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26570, d199571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26570, d199571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26571 q = 1) (hb : d199572 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26571, d199572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26571, d199572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199578 q = 1) (hb : d241063 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199579 q = 1) (hb : d241064 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199580 q = 1) (hb : d241065 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199580, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199580, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199590 q = 1) (hb : d241067 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199590, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199590, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199669 q = 1) (hb : d241068 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199669, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199669, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59284 (p : Pattern) (ha : d199675 p = 1) (hb : d241137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199666 q = 1) (hb : d241132 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199666, d241132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59282 q ha hb
    | true =>
      simp only [d199666, d241132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59263 q ha hb
  have h2 (q : Pattern) (ha : d199667 q = 1) (hb : d241133 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199667, d241133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199667, d241133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199668 q = 1) (hb : d241134 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199668, d241134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199668, d241134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199670 q = 1) (hb : d241069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199670, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59263 q ha hb
    | true =>
      simp only [d199670, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59283 q ha hb
  have h5 (q : Pattern) (ha : d199671 q = 1) (hb : d241070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199671, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199671, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199672 q = 1) (hb : d241071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199672, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199672, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199673 q = 1) (hb : d241135 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199673, d241135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199673, d241135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199592 q = 1) (hb : d241069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199592, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59263 q ha hb
    | true =>
      simp only [d199592, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59265 q ha hb
  have h9 (q : Pattern) (ha : d199593 q = 1) (hb : d241070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199593, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199593, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199594 q = 1) (hb : d241071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199594, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199594, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199596 q = 1) (hb : d241073 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59265 q ha hb
    | true =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59267 q ha hb
  have h12 (q : Pattern) (ha : d199597 q = 1) (hb : d241074 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199598 q = 1) (hb : d241075 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199599 q = 1) (hb : d241076 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199599, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199599, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d199674 q = 1) (hb : d241136 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199674, d241136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199674, d241136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d199675 q = 1) (hb : d241137 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199675, d241137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199675, d241137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro59285 (p : Pattern) (ha : d199681 p = 1) (hb : d241143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199676 q = 1) (hb : d241138 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199676, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59284 q ha hb
    | true =>
      simp only [d199676, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199677 q = 1) (hb : d241139 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199677, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199677, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199678 q = 1) (hb : d241140 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199678, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199678, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199679 q = 1) (hb : d241141 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199679, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199679, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199680 q = 1) (hb : d241142 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199680, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199680, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199681 q = 1) (hb : d241143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199681, d241143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199681, d241143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59286 (p : Pattern) (ha : d199687 p = 1) (hb : d241146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26558 q = 1) (hb : d199559 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26558, d199559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101508 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26559 q = 1) (hb : d199573 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26559, d199573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26559, d199573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26560 q = 1) (hb : d199574 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26560, d199574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26560, d199574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h9 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d26754 q = 1) (hb : d199684 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26754, d199684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26754, d199684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199685 q = 1) (hb : d239545 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d199685, d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199685, d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d199686 q = 1) (hb : d239546 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d199686, d239546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199686, d239546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d199687 q = 1) (hb : d241146 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d199687, d241146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d199687, d241146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro59287 (p : Pattern) (ha : d199693 p = 1) (hb : d241152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26568 q = 1) (hb : d199585 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59264 q ha hb
    | true =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26569 q = 1) (hb : d199586 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26570 q = 1) (hb : d199587 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26570, d199587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26570, d199587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26571 q = 1) (hb : d199588 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26571, d199588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26571, d199588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199578 q = 1) (hb : d241063 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199578, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199579 q = 1) (hb : d241064 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199579, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199589 q = 1) (hb : d241065 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199589, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199589, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199688 q = 1) (hb : d241147 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59286 q ha hb
    | true =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199689 q = 1) (hb : d241148 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199690 q = 1) (hb : d241149 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199690, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199690, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199691 q = 1) (hb : d241150 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199691, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199691, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d199692 q = 1) (hb : d241151 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199692, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199692, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d199693 q = 1) (hb : d241152 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199693, d241152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199693, d241152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59288 (p : Pattern) (ha : d199694 p = 1) (hb : d241153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199688 q = 1) (hb : d241147 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59286 q ha hb
    | true =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199689 q = 1) (hb : d241148 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199690 q = 1) (hb : d241149 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199690, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199690, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199691 q = 1) (hb : d241150 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199691, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199691, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199692 q = 1) (hb : d241151 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199692, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199692, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199694 q = 1) (hb : d241153 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199694, d241153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199694, d241153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59289 (p : Pattern) (ha : d199700 p = 1) (hb : d241159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199592 q = 1) (hb : d241069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199592, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59263 q ha hb
    | true =>
      simp only [d199592, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59265 q ha hb
  have h2 (q : Pattern) (ha : d199593 q = 1) (hb : d241070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199593, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199593, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199594 q = 1) (hb : d241071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199594, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199594, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199596 q = 1) (hb : d241073 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59265 q ha hb
    | true =>
      simp only [d199596, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59267 q ha hb
  have h5 (q : Pattern) (ha : d199597 q = 1) (hb : d241074 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199597, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199598 q = 1) (hb : d241075 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199598, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199599 q = 1) (hb : d241076 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199599, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199599, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199695 q = 1) (hb : d241154 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199695, d241154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59287 q ha hb
    | true =>
      simp only [d199695, d241154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59288 q ha hb
  have h9 (q : Pattern) (ha : d199696 q = 1) (hb : d241155 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199696, d241155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199696, d241155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199697 q = 1) (hb : d241156 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199697, d241156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199697, d241156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199698 q = 1) (hb : d241157 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199698, d241157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199698, d241157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199699 q = 1) (hb : d241158 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199699, d241158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199699, d241158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199700 q = 1) (hb : d241159 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199700, d241159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199700, d241159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro59290 (p : Pattern) (ha : d199706 p = 1) (hb : d241165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199701 q = 1) (hb : d241160 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199701, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59289 q ha hb
    | true =>
      simp only [d199701, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199702 q = 1) (hb : d241161 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199702, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199702, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199703 q = 1) (hb : d241162 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199703, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199703, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199704 q = 1) (hb : d241163 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199704, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199704, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199705 q = 1) (hb : d241164 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199705, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199705, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199706 q = 1) (hb : d241165 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199706, d241165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199706, d241165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59291 (p : Pattern) (ha : d199712 p = 1) (hb : d241171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199640 q = 1) (hb : d241117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199640, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59276 q ha hb
    | true =>
      simp only [d199640, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59277 q ha hb
  have h2 (q : Pattern) (ha : d199641 q = 1) (hb : d241118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199641, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199641, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199642 q = 1) (hb : d241119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199642, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199642, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199643 q = 1) (hb : d241120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199643, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199643, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199650 q = 1) (hb : d241127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199650, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59278 q ha hb
    | true =>
      simp only [d199650, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59279 q ha hb
  have h6 (q : Pattern) (ha : d199651 q = 1) (hb : d241128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199651, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199651, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199652 q = 1) (hb : d241129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199652, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199652, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199682 q = 1) (hb : d241144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199682, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59285 q ha hb
    | true =>
      simp only [d199682, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59270 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199617 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d199683 q = 1) (hb : d241145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199683, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d199707 q = 1) (hb : d241166 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199707, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59290 q ha hb
    | true =>
      simp only [d199707, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199708 q = 1) (hb : d241167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199708, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d199708, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d199709 q = 1) (hb : d241168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199709, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199710 q = 1) (hb : d241169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199710, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d199711 q = 1) (hb : d241170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199711, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d199712 q = 1) (hb : d241171 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199712, d241171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199712, d241171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro59292 (p : Pattern) (ha : d199713 p = 1) (hb : d241172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199609 q = 1) (hb : d241086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199610 q = 1) (hb : d241087 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199610, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199636 q = 1) (hb : d241113 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199636, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199636, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199713 q = 1) (hb : d241172 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199713, d241172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199713, d241172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59293 (p : Pattern) (ha : d199714 p = 1) (hb : d241173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199613 q = 1) (hb : d241090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199614 q = 1) (hb : d241091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199614, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199638 q = 1) (hb : d241115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199638, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199638, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199714 q = 1) (hb : d241173 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199714, d241173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199714, d241173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59294 (p : Pattern) (ha : d199719 p = 1) (hb : d241178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199609 q = 1) (hb : d241086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199609, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199644 q = 1) (hb : d241121 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199644, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199644, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199645 q = 1) (hb : d241122 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199645, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199645, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199719 q = 1) (hb : d241178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199719, d241178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199719, d241178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59295 (p : Pattern) (ha : d199720 p = 1) (hb : d241179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199607 q = 1) (hb : d241084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59269 q ha hb
    | true =>
      simp only [d199607, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199608 q = 1) (hb : d241085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199608, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199613 q = 1) (hb : d241090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199613, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199647 q = 1) (hb : d241124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199647, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199647, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199648 q = 1) (hb : d241125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199648, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199648, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199720 q = 1) (hb : d241179 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199720, d241179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199720, d241179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59296 (p : Pattern) (ha : d199724 p = 1) (hb : d241183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199676 q = 1) (hb : d241138 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199676, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59284 q ha hb
    | true =>
      simp only [d199676, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199677 q = 1) (hb : d241139 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199677, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199677, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199603 q = 1) (hb : d241080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59268 q ha hb
    | true =>
      simp only [d199603, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199604 q = 1) (hb : d241081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199604, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199678 q = 1) (hb : d241140 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199678, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199678, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199679 q = 1) (hb : d241141 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199679, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199679, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199680 q = 1) (hb : d241142 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199680, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199680, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199724 q = 1) (hb : d241183 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199724, d241183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199724, d241183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59297 (p : Pattern) (ha : d199727 p = 1) (hb : d241186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199701 q = 1) (hb : d241160 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199701, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59289 q ha hb
    | true =>
      simp only [d199701, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199702 q = 1) (hb : d241161 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199702, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199702, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199703 q = 1) (hb : d241162 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199703, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199703, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199704 q = 1) (hb : d241163 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199704, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199704, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199705 q = 1) (hb : d241164 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199705, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199705, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199727 q = 1) (hb : d241186 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199727, d241186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199727, d241186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59298 (p : Pattern) (ha : d199733 p = 1) (hb : d241192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199640 q = 1) (hb : d241117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199640, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59276 q ha hb
    | true =>
      simp only [d199640, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59277 q ha hb
  have h2 (q : Pattern) (ha : d199641 q = 1) (hb : d241118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199641, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199641, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199642 q = 1) (hb : d241119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199642, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199642, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199643 q = 1) (hb : d241120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199643, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199643, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199650 q = 1) (hb : d241127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199650, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59278 q ha hb
    | true =>
      simp only [d199650, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59279 q ha hb
  have h6 (q : Pattern) (ha : d199651 q = 1) (hb : d241128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199651, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199651, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199652 q = 1) (hb : d241129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199652, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199652, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199682 q = 1) (hb : d241144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199682, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59285 q ha hb
    | true =>
      simp only [d199682, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59270 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199617 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d199683 q = 1) (hb : d241145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199683, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d199707 q = 1) (hb : d241166 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199707, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59290 q ha hb
    | true =>
      simp only [d199707, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199708 q = 1) (hb : d241167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199708, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d199708, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d199709 q = 1) (hb : d241168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199709, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199710 q = 1) (hb : d241169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199710, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d199711 q = 1) (hb : d241170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199711, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d199715 q = 1) (hb : d241174 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199715, d241174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59292 q ha hb
    | true =>
      simp only [d199715, d241174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59293 q ha hb
  have h17 (q : Pattern) (ha : d199716 q = 1) (hb : d241175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199716, d241175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199716, d241175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199717 q = 1) (hb : d241176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199717, d241176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199717, d241176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d199718 q = 1) (hb : d241177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199718, d241177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199718, d241177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d199721 q = 1) (hb : d241180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199721, d241180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59294 q ha hb
    | true =>
      simp only [d199721, d241180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59295 q ha hb
  have h21 (q : Pattern) (ha : d199722 q = 1) (hb : d241181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199722, d241181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199722, d241181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199723 q = 1) (hb : d241182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199723, d241182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d199723, d241182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d199725 q = 1) (hb : d241184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199725, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59296 q ha hb
    | true =>
      simp only [d199725, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59273 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d199627 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d199726 q = 1) (hb : d241185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d199726, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d199728 q = 1) (hb : d241187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199728, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59297 q ha hb
    | true =>
      simp only [d199728, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d199729 q = 1) (hb : d241188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199729, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d199729, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d199730 q = 1) (hb : d241189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d199730, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d199731 q = 1) (hb : d241190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199731, d241190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d199731, d241190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d199732 q = 1) (hb : d241191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199732, d241191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d199732, d241191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d199733 q = 1) (hb : d241192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199733, d241192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199733, d241192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro59299 (p : Pattern) (ha : d199740 p = 1) (hb : d241199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199617 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59270 q ha hb
    | true =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59271 q ha hb
  have h2 (q : Pattern) (ha : d199618 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199618, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199618, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199619 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199619, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199619, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199620 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199620, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199620, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199621 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199621, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199621, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199735 q = 1) (hb : d241194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199735, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59271 q ha hb
    | true =>
      simp only [d199735, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199736 q = 1) (hb : d241195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199736, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199736, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199737 q = 1) (hb : d241196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199737, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199737, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199738 q = 1) (hb : d241197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199738, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199738, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199739 q = 1) (hb : d241198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199739, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199739, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199740 q = 1) (hb : d241199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199740, d241199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199740, d241199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59300 (p : Pattern) (ha : d199746 p = 1) (hb : d241205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199735 q = 1) (hb : d241194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199735, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59271 q ha hb
    | true =>
      simp only [d199735, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199736 q = 1) (hb : d241195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199736, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199736, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199737 q = 1) (hb : d241196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199737, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199737, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199738 q = 1) (hb : d241197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199738, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199738, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199739 q = 1) (hb : d241198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199739, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199739, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199741 q = 1) (hb : d241200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199741, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59274 q ha hb
    | true =>
      simp only [d199741, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199742 q = 1) (hb : d241201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199742, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199742, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199743 q = 1) (hb : d241202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199743, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199743, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199744 q = 1) (hb : d241203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199744, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199744, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199745 q = 1) (hb : d241204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199745, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199745, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199746 q = 1) (hb : d241205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199746, d241205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199746, d241205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59301 (p : Pattern) (ha : d199753 p = 1) (hb : d241212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199725 q = 1) (hb : d241184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199725, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59296 q ha hb
    | true =>
      simp only [d199725, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59273 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199627 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199726 q = 1) (hb : d241185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199726, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d199728 q = 1) (hb : d241187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199728, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59297 q ha hb
    | true =>
      simp only [d199728, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199729 q = 1) (hb : d241188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199729, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199729, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199730 q = 1) (hb : d241189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199730, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199751 q = 1) (hb : d241210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199751, d241210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199751, d241210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199752 q = 1) (hb : d241211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199752, d241211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199752, d241211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199753 q = 1) (hb : d241212 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199753, d241212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199753, d241212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro59302 (p : Pattern) (ha : d199755 p = 1) (hb : d241214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199741 q = 1) (hb : d241200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199741, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59274 q ha hb
    | true =>
      simp only [d199741, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199742 q = 1) (hb : d241201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199742, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199742, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199743 q = 1) (hb : d241202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199743, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199743, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199744 q = 1) (hb : d241203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199744, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199744, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199745 q = 1) (hb : d241204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199745, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199745, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199755 q = 1) (hb : d241214 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199755, d241214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199755, d241214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59303 (p : Pattern) (ha : d199779 p = 1) (hb : d241221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26834 q = 1) (hb : d199761 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26834, d199761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26834, d199761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59280 q ha hb
  have h2 (q : Pattern) (ha : d26653 q = 1) (hb : d199654 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26653, d199654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59280 q ha hb
    | true =>
      simp only [d26653, d199654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26835 q = 1) (hb : d199762 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26835, d199762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26835, d199762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26654 q = 1) (hb : d199655 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26654, d199655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26654, d199655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26836 q = 1) (hb : d199763 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26836, d199763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26836, d199763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26837 q = 1) (hb : d199764 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26837, d199764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26837, d199764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26843 q = 1) (hb : d199765 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26843, d199765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26843, d199765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59261 q ha hb
  have h8 (q : Pattern) (ha : d26659 q = 1) (hb : d199552 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59261 q ha hb
    | true =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26844 q = 1) (hb : d199766 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26844, d199766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26844, d199766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26660 q = 1) (hb : d199553 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26845 q = 1) (hb : d199767 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26845, d199767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26845, d199767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26846 q = 1) (hb : d199768 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26846, d199768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26846, d199768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d199769 q = 1) (hb : d241220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199769, d241220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d199769, d241220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d26843 q = 1) (hb : d199770 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26843, d199770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26843, d199770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59281 q ha hb
  have h15 (q : Pattern) (ha : d26659 q = 1) (hb : d199660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26659, d199660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59281 q ha hb
    | true =>
      simp only [d26659, d199660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d26844 q = 1) (hb : d199771 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26844, d199771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26844, d199771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26660 q = 1) (hb : d199661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26660, d199661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26660, d199661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26845 q = 1) (hb : d199772 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26845, d199772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26845, d199772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d26846 q = 1) (hb : d199773 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26846, d199773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d26846, d199773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d26847 q = 1) (hb : d199774 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26847, d199774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26847, d199774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
  have h21 (q : Pattern) (ha : d26568 q = 1) (hb : d199569 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
    | true =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d26848 q = 1) (hb : d199775 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26848, d199775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d26848, d199775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26569 q = 1) (hb : d199570 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d26849 q = 1) (hb : d199776 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26849, d199776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d26849, d199776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d26850 q = 1) (hb : d199777 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26850, d199777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d26850, d199777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d26851 q = 1) (hb : d199778 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26851, d199778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d26851, d199778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d199779 q = 1) (hb : d241221 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199779, d241221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199779, d241221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro59304 (p : Pattern) (ha : d199790 p = 1) (hb : d241227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26843 q = 1) (hb : d199765 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26843, d199765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26843, d199765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59261 q ha hb
  have h2 (q : Pattern) (ha : d26659 q = 1) (hb : d199552 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59261 q ha hb
    | true =>
      simp only [d26659, d199552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26844 q = 1) (hb : d199766 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26844, d199766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26844, d199766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26660 q = 1) (hb : d199553 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26660, d199553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26845 q = 1) (hb : d199767 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26845, d199767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26845, d199767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26846 q = 1) (hb : d199768 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26846, d199768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26846, d199768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26847 q = 1) (hb : d199780 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26847, d199780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26847, d199780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59259 q ha hb
  have h8 (q : Pattern) (ha : d26568 q = 1) (hb : d199563 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59259 q ha hb
    | true =>
      simp only [d26568, d199563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26848 q = 1) (hb : d199781 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26848, d199781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26848, d199781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26569 q = 1) (hb : d199564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26569, d199564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26849 q = 1) (hb : d199782 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26849, d199782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26849, d199782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26850 q = 1) (hb : d199783 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26850, d199783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26850, d199783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26851 q = 1) (hb : d199784 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26851, d199784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26851, d199784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26847 q = 1) (hb : d199774 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26847, d199774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26847, d199774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
  have h15 (q : Pattern) (ha : d26568 q = 1) (hb : d199569 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
    | true =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d26848 q = 1) (hb : d199775 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26848, d199775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26848, d199775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26569 q = 1) (hb : d199570 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26849 q = 1) (hb : d199776 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26849, d199776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26849, d199776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d26850 q = 1) (hb : d199777 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26850, d199777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d26850, d199777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d199785 q = 1) (hb : d241222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
  have h21 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d199786 q = 1) (hb : d241223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d199787 q = 1) (hb : d241224 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d199788 q = 1) (hb : d241225 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d199789 q = 1) (hb : d241226 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199789, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d199789, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d199790 q = 1) (hb : d241227 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199790, d241227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d199790, d241227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro59305 (p : Pattern) (ha : d199795 p = 1) (hb : d241232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26847 q = 1) (hb : d199774 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26847, d199774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26847, d199774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
  have h2 (q : Pattern) (ha : d26568 q = 1) (hb : d199569 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59260 q ha hb
    | true =>
      simp only [d26568, d199569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26848 q = 1) (hb : d199775 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26848, d199775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26848, d199775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26569 q = 1) (hb : d199570 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26569, d199570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26849 q = 1) (hb : d199776 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26849, d199776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26849, d199776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26850 q = 1) (hb : d199777 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26850, d199777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26850, d199777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d199785 q = 1) (hb : d241222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
  have h8 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199786 q = 1) (hb : d241223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199787 q = 1) (hb : d241224 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d199788 q = 1) (hb : d241225 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d199789 q = 1) (hb : d241226 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199789, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d199789, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199794 q = 1) (hb : d241231 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199794, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199794, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d199795 q = 1) (hb : d241232 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199795, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199795, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59306 (p : Pattern) (ha : d199805 p = 1) (hb : d241232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26847 q = 1) (hb : d199800 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26847, d199800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26847, d199800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59264 q ha hb
  have h2 (q : Pattern) (ha : d26568 q = 1) (hb : d199585 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59264 q ha hb
    | true =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26848 q = 1) (hb : d199801 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26848, d199801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26848, d199801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26569 q = 1) (hb : d199586 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26849 q = 1) (hb : d199802 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26849, d199802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26849, d199802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26850 q = 1) (hb : d199803 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26850, d199803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26850, d199803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d199785 q = 1) (hb : d241222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
  have h8 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199786 q = 1) (hb : d241223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199787 q = 1) (hb : d241224 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d199788 q = 1) (hb : d241225 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d199804 q = 1) (hb : d241226 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199804, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d199804, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199794 q = 1) (hb : d241231 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199794, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199794, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d199805 q = 1) (hb : d241232 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199805, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199805, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59307 (p : Pattern) (ha : d199809 p = 1) (hb : d241237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199785 q = 1) (hb : d241222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
  have h2 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199786 q = 1) (hb : d241223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199787 q = 1) (hb : d241224 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199788 q = 1) (hb : d241225 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199794 q = 1) (hb : d241231 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199794, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199794, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1883 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1883, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1883, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59266 q ha hb
  have h9 (q : Pattern) (ha : d1597 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59266 q ha hb
    | true =>
      simp only [d1597, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1884 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1884, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1884, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1598 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1598, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1885 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1885, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1886 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1886, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1887 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1887, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d199809 q = 1) (hb : d241237 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199809, d241237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199809, d241237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro59308 (p : Pattern) (ha : d199815 p = 1) (hb : d241243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199791 q = 1) (hb : d241228 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199791, d241228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59303 q ha hb
    | true =>
      simp only [d199791, d241228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59304 q ha hb
  have h2 (q : Pattern) (ha : d199792 q = 1) (hb : d241229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199792, d241229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199792, d241229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199793 q = 1) (hb : d241230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199793, d241230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199793, d241230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199796 q = 1) (hb : d241233 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199796, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59304 q ha hb
    | true =>
      simp only [d199796, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59305 q ha hb
  have h5 (q : Pattern) (ha : d199797 q = 1) (hb : d241234 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199797, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199797, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199798 q = 1) (hb : d241235 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199798, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199798, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199799 q = 1) (hb : d241236 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199799, d241236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199799, d241236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199806 q = 1) (hb : d241233 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199806, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59304 q ha hb
    | true =>
      simp only [d199806, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59306 q ha hb
  have h9 (q : Pattern) (ha : d199807 q = 1) (hb : d241234 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199807, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199807, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199808 q = 1) (hb : d241235 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199808, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199808, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199810 q = 1) (hb : d241238 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59306 q ha hb
    | true =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59307 q ha hb
  have h12 (q : Pattern) (ha : d199811 q = 1) (hb : d241239 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199812 q = 1) (hb : d241240 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199813 q = 1) (hb : d241241 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199813, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199813, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d199814 q = 1) (hb : d241242 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199814, d241242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199814, d241242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d199815 q = 1) (hb : d241243 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199815, d241243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199815, d241243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro59309 (p : Pattern) (ha : d199820 p = 1) (hb : d241248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199806 q = 1) (hb : d241233 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199806, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59304 q ha hb
    | true =>
      simp only [d199806, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59306 q ha hb
  have h2 (q : Pattern) (ha : d199807 q = 1) (hb : d241234 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199807, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199807, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199808 q = 1) (hb : d241235 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199808, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199808, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199810 q = 1) (hb : d241238 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59306 q ha hb
    | true =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59307 q ha hb
  have h5 (q : Pattern) (ha : d199811 q = 1) (hb : d241239 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199812 q = 1) (hb : d241240 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199813 q = 1) (hb : d241241 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199813, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199813, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199818 q = 1) (hb : d241246 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199818, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199818, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199819 q = 1) (hb : d241247 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199819, d241247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199819, d241247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199820 q = 1) (hb : d241248 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199820, d241248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199820, d241248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro59310 (p : Pattern) (ha : d199826 p = 1) (hb : d241254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199816 q = 1) (hb : d241244 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199816, d241244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59308 q ha hb
    | true =>
      simp only [d199816, d241244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199817 q = 1) (hb : d241245 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199817, d241245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199817, d241245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199821 q = 1) (hb : d241249 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199821, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59309 q ha hb
    | true =>
      simp only [d199821, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199822 q = 1) (hb : d241250 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199822, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199822, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199823 q = 1) (hb : d241251 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199823, d241251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199823, d241251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199824 q = 1) (hb : d241252 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199824, d241252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199824, d241252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199825 q = 1) (hb : d241253 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199825, d241253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199825, d241253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199826 q = 1) (hb : d241254 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199826, d241254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199826, d241254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59311 (p : Pattern) (ha : d199828 p = 1) (hb : d241256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199810 q = 1) (hb : d241238 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59306 q ha hb
    | true =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59307 q ha hb
  have h2 (q : Pattern) (ha : d199811 q = 1) (hb : d241239 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199812 q = 1) (hb : d241240 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199818 q = 1) (hb : d241246 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199818, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199818, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199827 q = 1) (hb : d241255 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199827, d241255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199827, d241255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199828 q = 1) (hb : d241256 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199828, d241256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199828, d241256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59312 (p : Pattern) (ha : d199834 p = 1) (hb : d241262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199821 q = 1) (hb : d241249 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199821, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59309 q ha hb
    | true =>
      simp only [d199821, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199822 q = 1) (hb : d241250 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199822, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199822, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199829 q = 1) (hb : d241257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199829, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59311 q ha hb
    | true =>
      simp only [d199829, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199830 q = 1) (hb : d241258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199830, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199830, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199831 q = 1) (hb : d241259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199831, d241259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199831, d241259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199832 q = 1) (hb : d241260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199832, d241260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199832, d241260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199833 q = 1) (hb : d241261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199833, d241261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199833, d241261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199834 q = 1) (hb : d241262 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199834, d241262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199834, d241262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59313 (p : Pattern) (ha : d199847 p = 1) (hb : d241270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26847 q = 1) (hb : d199800 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26847, d199800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26847, d199800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59264 q ha hb
  have h2 (q : Pattern) (ha : d26568 q = 1) (hb : d199585 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59264 q ha hb
    | true =>
      simp only [d26568, d199585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26848 q = 1) (hb : d199801 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26848, d199801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26848, d199801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26569 q = 1) (hb : d199586 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26569, d199586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26849 q = 1) (hb : d199802 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26849, d199802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26849, d199802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26850 q = 1) (hb : d199803 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26850, d199803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26850, d199803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d199785 q = 1) (hb : d241222 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199785, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
  have h8 (q : Pattern) (ha : d199576 q = 1) (hb : d241061 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59262 q ha hb
    | true =>
      simp only [d199576, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199786 q = 1) (hb : d241223 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199786, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199577 q = 1) (hb : d241062 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199577, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199787 q = 1) (hb : d241224 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199787, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d199788 q = 1) (hb : d241225 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d199788, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d199804 q = 1) (hb : d241226 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199804, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d199804, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199842 q = 1) (hb : d241265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199842, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199842, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59286 q ha hb
  have h15 (q : Pattern) (ha : d199688 q = 1) (hb : d241147 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59286 q ha hb
    | true =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d199843 q = 1) (hb : d241266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199843, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d199843, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199689 q = 1) (hb : d241148 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d199844 q = 1) (hb : d241267 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199844, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199844, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d199845 q = 1) (hb : d241268 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199845, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d199845, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d199846 q = 1) (hb : d241269 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199846, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d199846, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d199847 q = 1) (hb : d241270 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199847, d241270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199847, d241270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro59314 (p : Pattern) (ha : d199848 p = 1) (hb : d241271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199842 q = 1) (hb : d241265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199842, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199842, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59286 q ha hb
  have h2 (q : Pattern) (ha : d199688 q = 1) (hb : d241147 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59286 q ha hb
    | true =>
      simp only [d199688, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199843 q = 1) (hb : d241266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199843, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199843, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199689 q = 1) (hb : d241148 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199689, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199844 q = 1) (hb : d241267 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199844, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199844, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199845 q = 1) (hb : d241268 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199845, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199845, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199846 q = 1) (hb : d241269 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199846, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199846, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199848 q = 1) (hb : d241271 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199848, d241271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199848, d241271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59315 (p : Pattern) (ha : d199854 p = 1) (hb : d241277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199806 q = 1) (hb : d241233 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199806, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59304 q ha hb
    | true =>
      simp only [d199806, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59306 q ha hb
  have h2 (q : Pattern) (ha : d199807 q = 1) (hb : d241234 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199807, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199807, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199808 q = 1) (hb : d241235 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199808, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199808, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199810 q = 1) (hb : d241238 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59306 q ha hb
    | true =>
      simp only [d199810, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59307 q ha hb
  have h5 (q : Pattern) (ha : d199811 q = 1) (hb : d241239 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199811, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199812 q = 1) (hb : d241240 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199812, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199813 q = 1) (hb : d241241 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199813, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199813, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199849 q = 1) (hb : d241272 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199849, d241272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59313 q ha hb
    | true =>
      simp only [d199849, d241272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59314 q ha hb
  have h9 (q : Pattern) (ha : d199850 q = 1) (hb : d241273 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199850, d241273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199850, d241273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199851 q = 1) (hb : d241274 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199851, d241274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199851, d241274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199852 q = 1) (hb : d241275 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199852, d241275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199852, d241275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199853 q = 1) (hb : d241276 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199853, d241276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199853, d241276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199854 q = 1) (hb : d241277 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199854, d241277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199854, d241277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro59316 (p : Pattern) (ha : d199860 p = 1) (hb : d241283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199855 q = 1) (hb : d241278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199855, d241278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59315 q ha hb
    | true =>
      simp only [d199855, d241278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199856 q = 1) (hb : d241279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199856, d241279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199856, d241279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199857 q = 1) (hb : d241280 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199857, d241280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199857, d241280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199858 q = 1) (hb : d241281 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199858, d241281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199858, d241281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199859 q = 1) (hb : d241282 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199859, d241282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199859, d241282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199860 q = 1) (hb : d241283 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199860, d241283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199860, d241283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59317 (p : Pattern) (ha : d199866 p = 1) (hb : d241289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199835 q = 1) (hb : d241263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199835, d241263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59310 q ha hb
    | true =>
      simp only [d199835, d241263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59312 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199841 q = 1) (hb : d241264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199841, d241264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199841, d241264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d199861 q = 1) (hb : d241284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199861, d241284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59316 q ha hb
    | true =>
      simp only [d199861, d241284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199862 q = 1) (hb : d241285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199862, d241285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199862, d241285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199863 q = 1) (hb : d241286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199863, d241286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199863, d241286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199864 q = 1) (hb : d241287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199864, d241287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199864, d241287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199865 q = 1) (hb : d241288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199865, d241288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199865, d241288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199866 q = 1) (hb : d241289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199866, d241289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199866, d241289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro59318 (p : Pattern) (ha : d199839 p = 1) (hb : d241294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199829 q = 1) (hb : d241257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199829, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59311 q ha hb
    | true =>
      simp only [d199829, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199830 q = 1) (hb : d241258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199830, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199830, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199836 q = 1) (hb : d241291 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199836, d241291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199836, d241291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199837 q = 1) (hb : d241292 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199837, d241292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199837, d241292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199838 q = 1) (hb : d241293 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199838, d241293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199838, d241293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199839 q = 1) (hb : d241294 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199839, d241294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199839, d241294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59319 (p : Pattern) (ha : d199873 p = 1) (hb : d241300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199868 q = 1) (hb : d241295 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199868, d241295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59318 q ha hb
    | true =>
      simp only [d199868, d241295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199869 q = 1) (hb : d241296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199869, d241296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199869, d241296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199870 q = 1) (hb : d241297 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199870, d241297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199870, d241297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199871 q = 1) (hb : d241298 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199871, d241298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199871, d241298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199872 q = 1) (hb : d241299 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199872, d241299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199872, d241299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199873 q = 1) (hb : d241300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199873, d241300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199873, d241300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59320 (p : Pattern) (ha : d199879 p = 1) (hb : d241306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199623 q = 1) (hb : d241100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199623, d241100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199623, d241100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59272 q ha hb
  have h2 (q : Pattern) (ha : d199624 q = 1) (hb : d241101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199624, d241101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199624, d241101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199633 q = 1) (hb : d241110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199633, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59272 q ha hb
    | true =>
      simp only [d199633, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59275 q ha hb
  have h4 (q : Pattern) (ha : d199634 q = 1) (hb : d241111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199634, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199634, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199635 q = 1) (hb : d241112 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199635, d241112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199635, d241112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199734 q = 1) (hb : d241193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199734, d241193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59291 q ha hb
    | true =>
      simp only [d199734, d241193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59298 q ha hb
  have h7 (q : Pattern) (ha : d199747 q = 1) (hb : d241206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199747, d241206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59299 q ha hb
    | true =>
      simp only [d199747, d241206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59300 q ha hb
  have h8 (q : Pattern) (ha : d199748 q = 1) (hb : d241207 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199748, d241207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199748, d241207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199749 q = 1) (hb : d241208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199749, d241208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199749, d241208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d199750 q = 1) (hb : d241209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199750, d241209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199750, d241209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199754 q = 1) (hb : d241213 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199754, d241213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199754, d241213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59301 q ha hb
  have h12 (q : Pattern) (ha : d199756 q = 1) (hb : d241215 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199756, d241215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199756, d241215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59302 q ha hb
  have h13 (q : Pattern) (ha : d199757 q = 1) (hb : d241216 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199757, d241216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d199757, d241216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199758 q = 1) (hb : d241217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199758, d241217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199758, d241217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d199759 q = 1) (hb : d241218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199759, d241218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d199759, d241218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d199760 q = 1) (hb : d241219 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199760, d241219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199760, d241219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199867 q = 1) (hb : d241290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199867, d241290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199867, d241290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59317 q ha hb
  have h18 (q : Pattern) (ha : d199874 q = 1) (hb : d241301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199874, d241301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199874, d241301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59319 q ha hb
  have h19 (q : Pattern) (ha : d199875 q = 1) (hb : d241302 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199875, d241302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199875, d241302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d199876 q = 1) (hb : d241303 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199876, d241303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d199876, d241303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d199877 q = 1) (hb : d241304 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199877, d241304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d199877, d241304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d199878 q = 1) (hb : d241305 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199878, d241305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d199878, d241305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d199879 q = 1) (hb : d241306 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199879, d241306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199879, d241306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro59321 (p : Pattern) (ha : d199885 p = 1) (hb : d241312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199880 q = 1) (hb : d241307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199880, d241307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199880, d241307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59320 q ha hb
  have h2 (q : Pattern) (ha : d199881 q = 1) (hb : d241308 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199881, d241308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199881, d241308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199882 q = 1) (hb : d241309 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199882, d241309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199882, d241309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199883 q = 1) (hb : d241310 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199883, d241310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199883, d241310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199884 q = 1) (hb : d241311 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199884, d241311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199884, d241311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199885 q = 1) (hb : d241312 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199885, d241312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199885, d241312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59322 (p : Pattern) (ha : d27014 p = 1) (hb : d199890 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d10349 q = 1) (hb : d101670 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10350 q = 1) (hb : d101671 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10351 q = 1) (hb : d101672 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27014 q = 1) (hb : d199890 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27014, d199890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27014, d199890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59323 (p : Pattern) (ha : d27019 p = 1) (hb : d199895 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d10349 q = 1) (hb : d101670 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10350 q = 1) (hb : d101671 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10351 q = 1) (hb : d101672 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
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
        exact h1 q ha hb
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
  have h10 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d5716 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d5717 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d27019 q = 1) (hb : d199895 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27019, d199895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27019, d199895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro59324 (p : Pattern) (ha : d199901 p = 1) (hb : d241317 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d5716 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5717 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h8 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h9 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2076 q = 1) (hb : d53355 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d2077 q = 1) (hb : d101730 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2077, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2077, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2078 q = 1) (hb : d101731 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2078, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2078, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d199901 q = 1) (hb : d241317 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d199901, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d199901, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro59325 (p : Pattern) (ha : d199907 p = 1) (hb : d241323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27015 q = 1) (hb : d199891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59322 q ha hb
    | true =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27016 q = 1) (hb : d199892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27017 q = 1) (hb : d199893 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27017, d199893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27017, d199893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27018 q = 1) (hb : d199894 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27018, d199894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27018, d199894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27022 q = 1) (hb : d199898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27023 q = 1) (hb : d199899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27024 q = 1) (hb : d199900 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27024, d199900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27024, d199900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199902 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
    | true =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199903 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199904 q = 1) (hb : d241320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199904, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199904, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199905 q = 1) (hb : d241321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199905, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199905, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d199906 q = 1) (hb : d241322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199906, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d199906, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d199907 q = 1) (hb : d241323 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199907, d241323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199907, d241323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59326 (p : Pattern) (ha : d199911 p = 1) (hb : d241317 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5716 q = 1) (hb : d199909 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d199909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5716, d199909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5717 q = 1) (hb : d199910 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d199910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5717, d199910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h9 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h10 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2076 q = 1) (hb : d53355 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2077 q = 1) (hb : d101730 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2077, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2077, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2078 q = 1) (hb : d101731 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2078, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2078, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d199911 q = 1) (hb : d241317 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d199911, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d199911, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro59327 (p : Pattern) (ha : d199918 p = 1) (hb : d241325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27022 q = 1) (hb : d199898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27023 q = 1) (hb : d199899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d199912 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
    | true =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199913 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199914 q = 1) (hb : d241320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199914, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199914, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199915 q = 1) (hb : d241321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199915, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199915, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199916 q = 1) (hb : d241322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199916, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199916, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199902 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
    | true =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199903 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d199904 q = 1) (hb : d241320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199904, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199904, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199905 q = 1) (hb : d241321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199905, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199905, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d199917 q = 1) (hb : d241324 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199917, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199917, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d199918 q = 1) (hb : d241325 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199918, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199918, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59328 (p : Pattern) (ha : d2079 p = 1) (hb : d101732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h2 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h3 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2076 q = 1) (hb : d53355 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2077 q = 1) (hb : d101730 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2077, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2077, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2078 q = 1) (hb : d101731 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2078, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2078, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2079 q = 1) (hb : d101732 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2079, d101732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2079, d101732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro59329 (p : Pattern) (ha : d199923 p = 1) (hb : d241329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199912 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
    | true =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199913 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199914 q = 1) (hb : d241320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199914, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199914, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199915 q = 1) (hb : d241321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199915, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199915, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199922 q = 1) (hb : d241324 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199922, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199922, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d2080 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59328 q ha hb
    | true =>
      simp only [d2080, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2081 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2081, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2082 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2082, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2082, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2083 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2083, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2083, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2084 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2084, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2084, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d199923 q = 1) (hb : d241329 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199923, d241329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199923, d241329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro59330 (p : Pattern) (ha : d199930 p = 1) (hb : d241336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199919 q = 1) (hb : d241326 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199919, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59325 q ha hb
    | true =>
      simp only [d199919, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59327 q ha hb
  have h2 (q : Pattern) (ha : d199920 q = 1) (hb : d241327 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199920, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199920, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199921 q = 1) (hb : d241328 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199921, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199921, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199924 q = 1) (hb : d241330 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59327 q ha hb
    | true =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59329 q ha hb
  have h5 (q : Pattern) (ha : d199925 q = 1) (hb : d241331 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199926 q = 1) (hb : d241332 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199927 q = 1) (hb : d241333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199927, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199927, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199928 q = 1) (hb : d241334 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199928, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199928, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199929 q = 1) (hb : d241335 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199929, d241335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199929, d241335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199930 q = 1) (hb : d241336 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199930, d241336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199930, d241336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro59331 (p : Pattern) (ha : d199934 p = 1) (hb : d241340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199924 q = 1) (hb : d241330 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59327 q ha hb
    | true =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59329 q ha hb
  have h2 (q : Pattern) (ha : d199925 q = 1) (hb : d241331 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199926 q = 1) (hb : d241332 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199928 q = 1) (hb : d241334 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199928, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199928, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199933 q = 1) (hb : d241339 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199933, d241339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199933, d241339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199934 q = 1) (hb : d241340 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199934, d241340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199934, d241340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59332 (p : Pattern) (ha : d199940 p = 1) (hb : d241346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199937 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199938 q = 1) (hb : d241344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199939 q = 1) (hb : d241345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199939, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199939, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199940 q = 1) (hb : d241346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199940, d241346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199940, d241346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59333 (p : Pattern) (ha : d199944 p = 1) (hb : d241350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199941 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199942 q = 1) (hb : d241348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199943 q = 1) (hb : d241349 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199943, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199943, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199944 q = 1) (hb : d241350 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199944, d241350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199944, d241350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59334 (p : Pattern) (ha : d199950 p = 1) (hb : d241356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199945 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59332 q ha hb
    | true =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59333 q ha hb
  have h2 (q : Pattern) (ha : d199946 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199946, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199946, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199947 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199947, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199947, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199948 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199948, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199948, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199949 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199949, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199949, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199950 q = 1) (hb : d241356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199950, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199950, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59335 (p : Pattern) (ha : d199953 p = 1) (hb : d241359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199937 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199938 q = 1) (hb : d241344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199939 q = 1) (hb : d241345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199939, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199939, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199953 q = 1) (hb : d241359 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199953, d241359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199953, d241359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59336 (p : Pattern) (ha : d199954 p = 1) (hb : d241360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199941 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199942 q = 1) (hb : d241348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199943 q = 1) (hb : d241349 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199943, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199943, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199954 q = 1) (hb : d241360 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199954, d241360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199954, d241360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59337 (p : Pattern) (ha : d199960 p = 1) (hb : d241366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199945 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59332 q ha hb
    | true =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59333 q ha hb
  have h2 (q : Pattern) (ha : d199946 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199946, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199946, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199947 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199947, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199947, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199948 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199948, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199948, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199949 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199949, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199949, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199955 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59335 q ha hb
    | true =>
      simp only [d199955, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59336 q ha hb
  have h7 (q : Pattern) (ha : d199956 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199956, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199956, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199957 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199957, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199957, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199958 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199958, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199958, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199959 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199959, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199959, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199960 q = 1) (hb : d241366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199960, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199960, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59338 (p : Pattern) (ha : d199965 p = 1) (hb : d241371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199937 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199938 q = 1) (hb : d241344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199964 q = 1) (hb : d241370 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199964, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199964, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199965 q = 1) (hb : d241371 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199965, d241371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199965, d241371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59339 (p : Pattern) (ha : d199967 p = 1) (hb : d241373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199941 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199942 q = 1) (hb : d241348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199966 q = 1) (hb : d241372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199966, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199966, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199967 q = 1) (hb : d241373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199967, d241373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199967, d241373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59340 (p : Pattern) (ha : d199974 p = 1) (hb : d241380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199937 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199972 q = 1) (hb : d241378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199972, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199972, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199973 q = 1) (hb : d241379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199973, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199973, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199974 q = 1) (hb : d241380 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199974, d241380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199974, d241380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59341 (p : Pattern) (ha : d199977 p = 1) (hb : d241383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199941 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199975 q = 1) (hb : d241381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199975, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199975, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199976 q = 1) (hb : d241382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199976, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199976, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199977 q = 1) (hb : d241383 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199977, d241383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199977, d241383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59342 (p : Pattern) (ha : d27106 p = 1) (hb : d199982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27015 q = 1) (hb : d199891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59322 q ha hb
    | true =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27016 q = 1) (hb : d199892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27017 q = 1) (hb : d199893 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27017, d199893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27017, d199893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27018 q = 1) (hb : d199894 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27018, d199894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27018, d199894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27105 q = 1) (hb : d199981 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27105, d199981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27105, d199981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27022 q = 1) (hb : d199898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27023 q = 1) (hb : d199899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d27024 q = 1) (hb : d199900 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27024, d199900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27024, d199900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27106 q = 1) (hb : d199982 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27106, d199982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27106, d199982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59343 (p : Pattern) (ha : d199986 p = 1) (hb : d241325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27022 q = 1) (hb : d199898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27023 q = 1) (hb : d199899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d199902 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
    | true =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199903 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199904 q = 1) (hb : d241320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199904, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199904, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199905 q = 1) (hb : d241321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199905, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199905, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199906 q = 1) (hb : d241322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199906, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199906, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199917 q = 1) (hb : d241324 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199917, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199917, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d199986 q = 1) (hb : d241325 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d199986, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199986, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59344 (p : Pattern) (ha : d199992 p = 1) (hb : d241392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199983 q = 1) (hb : d241387 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199983, d241387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59342 q hb ha
    | true =>
      simp only [d199983, d241387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59325 q ha hb
  have h2 (q : Pattern) (ha : d199984 q = 1) (hb : d241388 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199984, d241388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199984, d241388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199985 q = 1) (hb : d241389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199985, d241389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199985, d241389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199987 q = 1) (hb : d241326 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199987, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59325 q ha hb
    | true =>
      simp only [d199987, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59343 q ha hb
  have h5 (q : Pattern) (ha : d199988 q = 1) (hb : d241327 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199988, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199988, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199989 q = 1) (hb : d241328 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199989, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199989, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199990 q = 1) (hb : d241390 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199990, d241390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199990, d241390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199919 q = 1) (hb : d241326 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199919, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59325 q ha hb
    | true =>
      simp only [d199919, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59327 q ha hb
  have h9 (q : Pattern) (ha : d199920 q = 1) (hb : d241327 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199920, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199920, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199921 q = 1) (hb : d241328 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199921, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199921, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d199924 q = 1) (hb : d241330 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59327 q ha hb
    | true =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59329 q ha hb
  have h12 (q : Pattern) (ha : d199925 q = 1) (hb : d241331 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199926 q = 1) (hb : d241332 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d199927 q = 1) (hb : d241333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199927, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199927, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d199991 q = 1) (hb : d241391 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d199991, d241391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199991, d241391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d199992 q = 1) (hb : d241392 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d199992, d241392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199992, d241392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro59345 (p : Pattern) (ha : d199998 p = 1) (hb : d241398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199993 q = 1) (hb : d241393 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199993, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59344 q ha hb
    | true =>
      simp only [d199993, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199994 q = 1) (hb : d241394 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199994, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199994, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199995 q = 1) (hb : d241395 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199995, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199995, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199996 q = 1) (hb : d241396 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199996, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199996, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199997 q = 1) (hb : d241397 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199997, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199997, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199998 q = 1) (hb : d241398 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199998, d241398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199998, d241398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59346 (p : Pattern) (ha : d200004 p = 1) (hb : d241401 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d5716 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5717 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h8 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d27181 q = 1) (hb : d200001 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d200001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27181, d200001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d200002 q = 1) (hb : d239849 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d200002, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d200002, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d200003 q = 1) (hb : d239850 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d200003, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200003, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d200004 q = 1) (hb : d241401 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d200004, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d200004, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro59347 (p : Pattern) (ha : d200010 p = 1) (hb : d241407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27022 q = 1) (hb : d199898 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d199898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27023 q = 1) (hb : d199899 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27023, d199899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d199912 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
    | true =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d199913 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199914 q = 1) (hb : d241320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d199914, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199914, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199915 q = 1) (hb : d241321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d199915, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199915, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d199916 q = 1) (hb : d241322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d199916, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199916, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200005 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200005, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59346 q ha hb
    | true =>
      simp only [d200005, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d200006 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200006, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200006, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d200007 q = 1) (hb : d241404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200007, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200007, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200008 q = 1) (hb : d241405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200008, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200008, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d200009 q = 1) (hb : d241406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200009, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200009, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d200010 q = 1) (hb : d241407 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200010, d241407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200010, d241407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59348 (p : Pattern) (ha : d200011 p = 1) (hb : d241401 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5716 q = 1) (hb : d199909 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d199909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5716, d199909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5717 q = 1) (hb : d199910 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d199910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5717, d199910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h9 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d27181 q = 1) (hb : d200001 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d200001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27181, d200001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d200002 q = 1) (hb : d239849 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d200002, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d200002, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d200003 q = 1) (hb : d239850 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d200003, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200003, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d200011 q = 1) (hb : d241401 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d200011, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d200011, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro59349 (p : Pattern) (ha : d200017 p = 1) (hb : d241408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200012 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200012, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59348 q ha hb
    | true =>
      simp only [d200012, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200013 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200013, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200013, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200014 q = 1) (hb : d241404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200014, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200014, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200015 q = 1) (hb : d241405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200015, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200015, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200016 q = 1) (hb : d241406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200016, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200016, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200017 q = 1) (hb : d241408 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200017, d241408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200017, d241408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59350 (p : Pattern) (ha : d200023 p = 1) (hb : d241414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199919 q = 1) (hb : d241326 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199919, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59325 q ha hb
    | true =>
      simp only [d199919, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59327 q ha hb
  have h2 (q : Pattern) (ha : d199920 q = 1) (hb : d241327 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199920, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199920, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199921 q = 1) (hb : d241328 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199921, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199921, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199924 q = 1) (hb : d241330 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59327 q ha hb
    | true =>
      simp only [d199924, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59329 q ha hb
  have h5 (q : Pattern) (ha : d199925 q = 1) (hb : d241331 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199925, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199926 q = 1) (hb : d241332 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199926, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199927 q = 1) (hb : d241333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d199927, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199927, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200018 q = 1) (hb : d241409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200018, d241409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59347 q ha hb
    | true =>
      simp only [d200018, d241409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59349 q ha hb
  have h9 (q : Pattern) (ha : d200019 q = 1) (hb : d241410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200019, d241410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200019, d241410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200020 q = 1) (hb : d241411 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200020, d241411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200020, d241411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200021 q = 1) (hb : d241412 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200021, d241412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200021, d241412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d200022 q = 1) (hb : d241413 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d200022, d241413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200022, d241413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200023 q = 1) (hb : d241414 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d200023, d241414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200023, d241414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro59351 (p : Pattern) (ha : d200029 p = 1) (hb : d241420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200024 q = 1) (hb : d241415 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200024, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59350 q ha hb
    | true =>
      simp only [d200024, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200025 q = 1) (hb : d241416 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200025, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200025, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200026 q = 1) (hb : d241417 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d200026, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200026, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200027 q = 1) (hb : d241418 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d200027, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200027, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200028 q = 1) (hb : d241419 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d200028, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200028, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200029 q = 1) (hb : d241420 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200029, d241420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200029, d241420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59352 (p : Pattern) (ha : d200035 p = 1) (hb : d241426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199968 q = 1) (hb : d241374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199968, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59338 q ha hb
    | true =>
      simp only [d199968, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59339 q ha hb
  have h2 (q : Pattern) (ha : d199969 q = 1) (hb : d241375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199969, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199969, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199970 q = 1) (hb : d241376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199970, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199970, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199971 q = 1) (hb : d241377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199971, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199971, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199978 q = 1) (hb : d241384 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199978, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59340 q ha hb
    | true =>
      simp only [d199978, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59341 q ha hb
  have h6 (q : Pattern) (ha : d199979 q = 1) (hb : d241385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199979, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199979, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199980 q = 1) (hb : d241386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199980, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199980, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199999 q = 1) (hb : d241399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199999, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59345 q ha hb
    | true =>
      simp only [d199999, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59332 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d200000 q = 1) (hb : d241400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200000, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d200030 q = 1) (hb : d241421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200030, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59351 q ha hb
    | true =>
      simp only [d200030, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d200031 q = 1) (hb : d241422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200031, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200031, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d200032 q = 1) (hb : d241423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200032, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200033 q = 1) (hb : d241424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200033, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200034 q = 1) (hb : d241425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200034, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200035 q = 1) (hb : d241426 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200035, d241426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200035, d241426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro59353 (p : Pattern) (ha : d200036 p = 1) (hb : d241427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199937 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199938 q = 1) (hb : d241344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199938, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199964 q = 1) (hb : d241370 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199964, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199964, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200036 q = 1) (hb : d241427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200036, d241427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200036, d241427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59354 (p : Pattern) (ha : d200037 p = 1) (hb : d241428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199941 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199942 q = 1) (hb : d241348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199942, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199966 q = 1) (hb : d241372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199966, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199966, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200037 q = 1) (hb : d241428 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200037, d241428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200037, d241428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59355 (p : Pattern) (ha : d200042 p = 1) (hb : d241433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199937 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199937, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199972 q = 1) (hb : d241378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199972, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199972, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199973 q = 1) (hb : d241379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199973, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199973, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d200042 q = 1) (hb : d241433 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200042, d241433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200042, d241433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59356 (p : Pattern) (ha : d200043 p = 1) (hb : d241434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199935 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59331 q ha hb
    | true =>
      simp only [d199935, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199936 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199936, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199941 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199941, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199975 q = 1) (hb : d241381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199975, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199975, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199976 q = 1) (hb : d241382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199976, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199976, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200043 q = 1) (hb : d241434 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200043, d241434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200043, d241434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59357 (p : Pattern) (ha : d200047 p = 1) (hb : d241438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199993 q = 1) (hb : d241393 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199993, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59344 q ha hb
    | true =>
      simp only [d199993, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d199994 q = 1) (hb : d241394 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199994, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199994, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199931 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59330 q ha hb
    | true =>
      simp only [d199931, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199932 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199932, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199995 q = 1) (hb : d241395 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d199995, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199995, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199996 q = 1) (hb : d241396 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d199996, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199996, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d199997 q = 1) (hb : d241397 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d199997, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199997, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d200047 q = 1) (hb : d241438 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200047, d241438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200047, d241438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59358 (p : Pattern) (ha : d200050 p = 1) (hb : d241441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200024 q = 1) (hb : d241415 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200024, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59350 q ha hb
    | true =>
      simp only [d200024, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200025 q = 1) (hb : d241416 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200025, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200025, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200026 q = 1) (hb : d241417 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d200026, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200026, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200027 q = 1) (hb : d241418 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d200027, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200027, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200028 q = 1) (hb : d241419 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d200028, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200028, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200050 q = 1) (hb : d241441 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200050, d241441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200050, d241441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59359 (p : Pattern) (ha : d200056 p = 1) (hb : d241447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199968 q = 1) (hb : d241374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199968, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59338 q ha hb
    | true =>
      simp only [d199968, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59339 q ha hb
  have h2 (q : Pattern) (ha : d199969 q = 1) (hb : d241375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199969, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199969, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199970 q = 1) (hb : d241376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199970, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199970, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199971 q = 1) (hb : d241377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199971, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199971, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199978 q = 1) (hb : d241384 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199978, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59340 q ha hb
    | true =>
      simp only [d199978, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59341 q ha hb
  have h6 (q : Pattern) (ha : d199979 q = 1) (hb : d241385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199979, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199979, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199980 q = 1) (hb : d241386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199980, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199980, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d199999 q = 1) (hb : d241399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199999, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59345 q ha hb
    | true =>
      simp only [d199999, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59332 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d200000 q = 1) (hb : d241400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200000, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d200030 q = 1) (hb : d241421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200030, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59351 q ha hb
    | true =>
      simp only [d200030, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d200031 q = 1) (hb : d241422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200031, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200031, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d200032 q = 1) (hb : d241423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200032, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200033 q = 1) (hb : d241424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200033, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200034 q = 1) (hb : d241425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200034, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200038 q = 1) (hb : d241429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200038, d241429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59353 q ha hb
    | true =>
      simp only [d200038, d241429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59354 q ha hb
  have h17 (q : Pattern) (ha : d200039 q = 1) (hb : d241430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200039, d241430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200039, d241430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200040 q = 1) (hb : d241431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200040, d241431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d200040, d241431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d200041 q = 1) (hb : d241432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200041, d241432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200041, d241432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200044 q = 1) (hb : d241435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200044, d241435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59355 q ha hb
    | true =>
      simp only [d200044, d241435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59356 q ha hb
  have h21 (q : Pattern) (ha : d200045 q = 1) (hb : d241436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200045, d241436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200045, d241436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d200046 q = 1) (hb : d241437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200046, d241437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d200046, d241437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d200048 q = 1) (hb : d241439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200048, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59357 q ha hb
    | true =>
      simp only [d200048, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59335 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d199955 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d200049 q = 1) (hb : d241440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d200049, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d200051 q = 1) (hb : d241442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200051, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59358 q ha hb
    | true =>
      simp only [d200051, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d200052 q = 1) (hb : d241443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200052, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d200052, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d200053 q = 1) (hb : d241444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d200053, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d200054 q = 1) (hb : d241445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200054, d241445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d200054, d241445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d200055 q = 1) (hb : d241446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200055, d241446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d200055, d241446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d200056 q = 1) (hb : d241447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200056, d241447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200056, d241447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro59360 (p : Pattern) (ha : d200063 p = 1) (hb : d241454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199945 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59332 q ha hb
    | true =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59333 q ha hb
  have h2 (q : Pattern) (ha : d199946 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199946, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199946, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199947 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199947, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199947, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d199948 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199948, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199948, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199949 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199949, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199949, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200058 q = 1) (hb : d241449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200058, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59333 q ha hb
    | true =>
      simp only [d200058, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d200059 q = 1) (hb : d241450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200059, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200059, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200060 q = 1) (hb : d241451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200060, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200060, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d200061 q = 1) (hb : d241452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200061, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200061, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200062 q = 1) (hb : d241453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200062, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200062, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200063 q = 1) (hb : d241454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200063, d241454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200063, d241454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59361 (p : Pattern) (ha : d200069 p = 1) (hb : d241460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200058 q = 1) (hb : d241449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200058, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59333 q ha hb
    | true =>
      simp only [d200058, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200059 q = 1) (hb : d241450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200059, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200059, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200060 q = 1) (hb : d241451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200060, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200060, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200061 q = 1) (hb : d241452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200061, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200061, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200062 q = 1) (hb : d241453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200062, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200062, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200064 q = 1) (hb : d241455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200064, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59336 q ha hb
    | true =>
      simp only [d200064, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d200065 q = 1) (hb : d241456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200065, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200065, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200066 q = 1) (hb : d241457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200066, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200066, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d200067 q = 1) (hb : d241458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200067, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200067, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200068 q = 1) (hb : d241459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200068, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200068, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200069 q = 1) (hb : d241460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200069, d241460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200069, d241460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro59362 (p : Pattern) (ha : d200076 p = 1) (hb : d241467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200048 q = 1) (hb : d241439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200048, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59357 q ha hb
    | true =>
      simp only [d200048, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59335 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200049 q = 1) (hb : d241440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200049, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d200051 q = 1) (hb : d241442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200051, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59358 q ha hb
    | true =>
      simp only [d200051, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200052 q = 1) (hb : d241443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200052, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200052, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200053 q = 1) (hb : d241444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200053, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200074 q = 1) (hb : d241465 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200074, d241465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200074, d241465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200075 q = 1) (hb : d241466 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200075, d241466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200075, d241466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200076 q = 1) (hb : d241467 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200076, d241467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200076, d241467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro59363 (p : Pattern) (ha : d200078 p = 1) (hb : d241469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200064 q = 1) (hb : d241455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200064, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59336 q ha hb
    | true =>
      simp only [d200064, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200065 q = 1) (hb : d241456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200065, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200065, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200066 q = 1) (hb : d241457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200066, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200066, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200067 q = 1) (hb : d241458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200067, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200067, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200068 q = 1) (hb : d241459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200068, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200068, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200078 q = 1) (hb : d241469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200078, d241469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200078, d241469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59364 (p : Pattern) (ha : d27277 p = 1) (hb : d200094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27267 q = 1) (hb : d200084 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d200084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27267, d200084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59322 q ha hb
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d199891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59322 q ha hb
    | true =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27268 q = 1) (hb : d200085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d200085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27268, d200085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27016 q = 1) (hb : d199892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27269 q = 1) (hb : d200086 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d200086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27269, d200086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27270 q = 1) (hb : d200087 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d200087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27270, d200087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27271 q = 1) (hb : d200088 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27271, d200088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27271, d200088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27272 q = 1) (hb : d200089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
  have h9 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d27273 q = 1) (hb : d200090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27274 q = 1) (hb : d200091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27275 q = 1) (hb : d200092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d27276 q = 1) (hb : d200093 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27276, d200093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27276, d200093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27277 q = 1) (hb : d200094 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27277, d200094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27277, d200094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59365 (p : Pattern) (ha : d200100 p = 1) (hb : d241480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27267 q = 1) (hb : d200084 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d200084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27267, d200084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59322 q ha hb
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d199891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59322 q ha hb
    | true =>
      simp only [d27015, d199891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27268 q = 1) (hb : d200085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d200085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27268, d200085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27016 q = 1) (hb : d199892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d199892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27269 q = 1) (hb : d200086 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d200086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27269, d200086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27270 q = 1) (hb : d200087 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d200087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27270, d200087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27272 q = 1) (hb : d200089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
  have h8 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27273 q = 1) (hb : d200090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27274 q = 1) (hb : d200091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27275 q = 1) (hb : d200092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d27276 q = 1) (hb : d200093 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27276, d200093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27276, d200093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200095 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200095, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200095, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
  have h15 (q : Pattern) (ha : d199902 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
    | true =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d200096 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200096, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d200096, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199903 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d200097 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200097, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200097, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200098 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200098, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d200098, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d200099 q = 1) (hb : d241479 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200099, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d200099, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d200100 q = 1) (hb : d241480 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200100, d241480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d200100, d241480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro59366 (p : Pattern) (ha : d200105 p = 1) (hb : d241485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d200089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d200090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d200091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d200092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d200095 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200095, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200095, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
  have h8 (q : Pattern) (ha : d199902 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
    | true =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d200096 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200096, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200096, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199903 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d200097 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200097, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200097, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d200098 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200098, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200098, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d200099 q = 1) (hb : d241479 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200099, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d200099, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200104 q = 1) (hb : d241484 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200104, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200104, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d200105 q = 1) (hb : d241485 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200105, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200105, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59367 (p : Pattern) (ha : d200115 p = 1) (hb : d241485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d200089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d200090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d200091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d200092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d200110 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200110, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200110, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
  have h8 (q : Pattern) (ha : d199912 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
    | true =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d200111 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200111, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200111, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199913 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d200112 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200112, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200112, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d200113 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200113, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200113, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d200114 q = 1) (hb : d241479 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200114, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d200114, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200095 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200095, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200095, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
  have h15 (q : Pattern) (ha : d199902 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59324 q ha hb
    | true =>
      simp only [d199902, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d200096 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200096, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d200096, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199903 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199903, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d200097 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200097, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200097, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200098 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200098, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d200098, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d200104 q = 1) (hb : d241484 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200104, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d200104, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d200115 q = 1) (hb : d241485 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200115, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200115, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro59368 (p : Pattern) (ha : d200120 p = 1) (hb : d241490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200110 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200110, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200110, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
  have h2 (q : Pattern) (ha : d199912 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
    | true =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200111 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200111, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200111, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199913 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200112 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200112, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200112, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200113 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200113, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200113, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d200119 q = 1) (hb : d241484 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200119, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200119, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d2361 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2361, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59328 q ha hb
  have h9 (q : Pattern) (ha : d2080 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59328 q ha hb
    | true =>
      simp only [d2080, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2362 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2362, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2081 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2081, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2363 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2363, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2364 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2364, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2365 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2365, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d200120 q = 1) (hb : d241490 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200120, d241490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200120, d241490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro59369 (p : Pattern) (ha : d200126 p = 1) (hb : d241496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200101 q = 1) (hb : d241481 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200101, d241481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59364 q hb ha
    | true =>
      simp only [d200101, d241481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59365 q ha hb
  have h2 (q : Pattern) (ha : d200102 q = 1) (hb : d241482 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200102, d241482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200102, d241482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200103 q = 1) (hb : d241483 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200103, d241483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200103, d241483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200106 q = 1) (hb : d241486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200106, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59365 q ha hb
    | true =>
      simp only [d200106, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59366 q ha hb
  have h5 (q : Pattern) (ha : d200107 q = 1) (hb : d241487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200107, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200107, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200108 q = 1) (hb : d241488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200108, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200108, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200109 q = 1) (hb : d241489 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200109, d241489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200109, d241489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200116 q = 1) (hb : d241486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200116, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59365 q ha hb
    | true =>
      simp only [d200116, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59367 q ha hb
  have h9 (q : Pattern) (ha : d200117 q = 1) (hb : d241487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200117, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200117, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200118 q = 1) (hb : d241488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200118, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200118, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200121 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59367 q ha hb
    | true =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59368 q ha hb
  have h12 (q : Pattern) (ha : d200122 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200123 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200124 q = 1) (hb : d241494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200124, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200124, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200125 q = 1) (hb : d241495 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d200125, d241495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200125, d241495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200126 q = 1) (hb : d241496 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d200126, d241496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200126, d241496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro59370 (p : Pattern) (ha : d200131 p = 1) (hb : d241501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200116 q = 1) (hb : d241486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200116, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59365 q ha hb
    | true =>
      simp only [d200116, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59367 q ha hb
  have h2 (q : Pattern) (ha : d200117 q = 1) (hb : d241487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200117, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200117, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200118 q = 1) (hb : d241488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200118, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200118, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200121 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59367 q ha hb
    | true =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59368 q ha hb
  have h5 (q : Pattern) (ha : d200122 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200123 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200124 q = 1) (hb : d241494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200124, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200124, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200129 q = 1) (hb : d241499 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200129, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200129, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d200130 q = 1) (hb : d241500 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d200130, d241500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200130, d241500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200131 q = 1) (hb : d241501 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d200131, d241501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200131, d241501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro59371 (p : Pattern) (ha : d200137 p = 1) (hb : d241507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200127 q = 1) (hb : d241497 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200127, d241497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59369 q ha hb
    | true =>
      simp only [d200127, d241497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200128 q = 1) (hb : d241498 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200128, d241498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200128, d241498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200132 q = 1) (hb : d241502 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200132, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59370 q ha hb
    | true =>
      simp only [d200132, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200133 q = 1) (hb : d241503 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200133, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200133, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200134 q = 1) (hb : d241504 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d200134, d241504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200134, d241504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200135 q = 1) (hb : d241505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d200135, d241505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200135, d241505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d200136 q = 1) (hb : d241506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d200136, d241506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200136, d241506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d200137 q = 1) (hb : d241507 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200137, d241507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200137, d241507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59372 (p : Pattern) (ha : d200139 p = 1) (hb : d241509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200121 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59367 q ha hb
    | true =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59368 q ha hb
  have h2 (q : Pattern) (ha : d200122 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200123 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200129 q = 1) (hb : d241499 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200129, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200129, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200138 q = 1) (hb : d241508 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d200138, d241508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200138, d241508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200139 q = 1) (hb : d241509 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d200139, d241509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200139, d241509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59373 (p : Pattern) (ha : d200145 p = 1) (hb : d241515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200132 q = 1) (hb : d241502 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200132, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59370 q ha hb
    | true =>
      simp only [d200132, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200133 q = 1) (hb : d241503 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200133, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200133, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200140 q = 1) (hb : d241510 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200140, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59372 q ha hb
    | true =>
      simp only [d200140, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200141 q = 1) (hb : d241511 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200141, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200141, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200142 q = 1) (hb : d241512 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d200142, d241512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200142, d241512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200143 q = 1) (hb : d241513 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d200143, d241513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200143, d241513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d200144 q = 1) (hb : d241514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d200144, d241514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200144, d241514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d200145 q = 1) (hb : d241515 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200145, d241515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200145, d241515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59374 (p : Pattern) (ha : d200158 p = 1) (hb : d241523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d200089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d200089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d199896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59323 q ha hb
    | true =>
      simp only [d27020, d199896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d200090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d200090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d199897 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d199897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d200091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d200091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d200092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d200092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d200110 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200110, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200110, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
  have h8 (q : Pattern) (ha : d199912 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59326 q ha hb
    | true =>
      simp only [d199912, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d200111 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200111, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200111, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199913 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199913, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d200112 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200112, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200112, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d200113 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200113, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200113, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d200114 q = 1) (hb : d241479 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200114, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d200114, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200153 q = 1) (hb : d241518 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200153, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200153, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59346 q ha hb
  have h15 (q : Pattern) (ha : d200005 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200005, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59346 q ha hb
    | true =>
      simp only [d200005, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d200154 q = 1) (hb : d241519 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200154, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d200154, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200006 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200006, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200006, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d200155 q = 1) (hb : d241520 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200155, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200155, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200156 q = 1) (hb : d241521 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200156, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d200156, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d200157 q = 1) (hb : d241522 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200157, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d200157, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d200158 q = 1) (hb : d241523 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200158, d241523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200158, d241523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro59375 (p : Pattern) (ha : d200164 p = 1) (hb : d241524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200159 q = 1) (hb : d241518 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200159, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200159, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59348 q ha hb
  have h2 (q : Pattern) (ha : d200012 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d200012, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59348 q ha hb
    | true =>
      simp only [d200012, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200160 q = 1) (hb : d241519 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200160, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200160, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200013 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d200013, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200013, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200161 q = 1) (hb : d241520 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d200161, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200161, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200162 q = 1) (hb : d241521 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d200162, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200162, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d200163 q = 1) (hb : d241522 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d200163, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200163, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d200164 q = 1) (hb : d241524 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d200164, d241524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200164, d241524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro59376 (p : Pattern) (ha : d200170 p = 1) (hb : d241530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200116 q = 1) (hb : d241486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200116, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59365 q ha hb
    | true =>
      simp only [d200116, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59367 q ha hb
  have h2 (q : Pattern) (ha : d200117 q = 1) (hb : d241487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200117, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200117, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200118 q = 1) (hb : d241488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200118, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200118, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200121 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59367 q ha hb
    | true =>
      simp only [d200121, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59368 q ha hb
  have h5 (q : Pattern) (ha : d200122 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200122, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200123 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200123, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200124 q = 1) (hb : d241494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200124, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200124, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200165 q = 1) (hb : d241525 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d200165, d241525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59374 q ha hb
    | true =>
      simp only [d200165, d241525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59375 q ha hb
  have h9 (q : Pattern) (ha : d200166 q = 1) (hb : d241526 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d200166, d241526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200166, d241526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200167 q = 1) (hb : d241527 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d200167, d241527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200167, d241527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200168 q = 1) (hb : d241528 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d200168, d241528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200168, d241528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d200169 q = 1) (hb : d241529 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d200169, d241529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200169, d241529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200170 q = 1) (hb : d241530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d200170, d241530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200170, d241530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro59377 (p : Pattern) (ha : d200176 p = 1) (hb : d241536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200171 q = 1) (hb : d241531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200171, d241531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59376 q ha hb
    | true =>
      simp only [d200171, d241531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200172 q = 1) (hb : d241532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200172, d241532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200172, d241532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200173 q = 1) (hb : d241533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d200173, d241533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200173, d241533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200174 q = 1) (hb : d241534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d200174, d241534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200174, d241534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200175 q = 1) (hb : d241535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d200175, d241535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200175, d241535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200176 q = 1) (hb : d241536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200176, d241536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200176, d241536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59378 (p : Pattern) (ha : d200182 p = 1) (hb : d241542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200146 q = 1) (hb : d241516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200146, d241516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59371 q ha hb
    | true =>
      simp only [d200146, d241516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59373 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200151 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200152 q = 1) (hb : d241517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200152, d241517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200152, d241517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d200177 q = 1) (hb : d241537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200177, d241537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59377 q ha hb
    | true =>
      simp only [d200177, d241537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200178 q = 1) (hb : d241538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200178, d241538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200178, d241538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200179 q = 1) (hb : d241539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200179, d241539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200179, d241539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200180 q = 1) (hb : d241540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200180, d241540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200180, d241540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200181 q = 1) (hb : d241541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200181, d241541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200181, d241541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200182 q = 1) (hb : d241542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200182, d241542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200182, d241542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro59379 (p : Pattern) (ha : d200150 p = 1) (hb : d241547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200140 q = 1) (hb : d241510 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d200140, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59372 q ha hb
    | true =>
      simp only [d200140, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200141 q = 1) (hb : d241511 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d200141, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200141, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200147 q = 1) (hb : d241544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d200147, d241544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200147, d241544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200148 q = 1) (hb : d241545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d200148, d241545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200148, d241545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200149 q = 1) (hb : d241546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d200149, d241546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200149, d241546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200150 q = 1) (hb : d241547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d200150, d241547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200150, d241547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59380 (p : Pattern) (ha : d200189 p = 1) (hb : d241553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200184 q = 1) (hb : d241548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200184, d241548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59379 q ha hb
    | true =>
      simp only [d200184, d241548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200185 q = 1) (hb : d241549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200185, d241549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200185, d241549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200186 q = 1) (hb : d241550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200186, d241550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200186, d241550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200187 q = 1) (hb : d241551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200187, d241551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200187, d241551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200188 q = 1) (hb : d241552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200188, d241552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200188, d241552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200189 q = 1) (hb : d241553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200189, d241553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200189, d241553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59381 (p : Pattern) (ha : d200195 p = 1) (hb : d241559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199951 q = 1) (hb : d241357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199951, d241357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199951, d241357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59334 q ha hb
  have h2 (q : Pattern) (ha : d199952 q = 1) (hb : d241358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199952, d241358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199952, d241358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d199961 q = 1) (hb : d241367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199961, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59334 q ha hb
    | true =>
      simp only [d199961, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59337 q ha hb
  have h4 (q : Pattern) (ha : d199962 q = 1) (hb : d241368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199962, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199962, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d199963 q = 1) (hb : d241369 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199963, d241369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d199963, d241369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200057 q = 1) (hb : d241448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200057, d241448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59352 q ha hb
    | true =>
      simp only [d200057, d241448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59359 q ha hb
  have h7 (q : Pattern) (ha : d200070 q = 1) (hb : d241461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200070, d241461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59360 q ha hb
    | true =>
      simp only [d200070, d241461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59361 q ha hb
  have h8 (q : Pattern) (ha : d200071 q = 1) (hb : d241462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200071, d241462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200071, d241462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200072 q = 1) (hb : d241463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200072, d241463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200072, d241463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d200073 q = 1) (hb : d241464 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200073, d241464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200073, d241464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200077 q = 1) (hb : d241468 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200077, d241468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200077, d241468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59362 q ha hb
  have h12 (q : Pattern) (ha : d200079 q = 1) (hb : d241470 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200079, d241470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200079, d241470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59363 q ha hb
  have h13 (q : Pattern) (ha : d200080 q = 1) (hb : d241471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200080, d241471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200080, d241471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200081 q = 1) (hb : d241472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200081, d241472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200081, d241472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d200082 q = 1) (hb : d241473 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200082, d241473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d200082, d241473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d200083 q = 1) (hb : d241474 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200083, d241474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200083, d241474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200183 q = 1) (hb : d241543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200183, d241543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200183, d241543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59378 q ha hb
  have h18 (q : Pattern) (ha : d200190 q = 1) (hb : d241554 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200190, d241554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200190, d241554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59380 q ha hb
  have h19 (q : Pattern) (ha : d200191 q = 1) (hb : d241555 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200191, d241555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d200191, d241555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200192 q = 1) (hb : d241556 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200192, d241556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d200192, d241556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d200193 q = 1) (hb : d241557 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200193, d241557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d200193, d241557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d200194 q = 1) (hb : d241558 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200194, d241558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d200194, d241558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d200195 q = 1) (hb : d241559 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d200195, d241559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200195, d241559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro59382 (p : Pattern) (ha : d200201 p = 1) (hb : d241565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200196 q = 1) (hb : d241560 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d200196, d241560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200196, d241560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59381 q ha hb
  have h2 (q : Pattern) (ha : d200197 q = 1) (hb : d241561 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d200197, d241561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200197, d241561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200198 q = 1) (hb : d241562 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d200198, d241562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200198, d241562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200199 q = 1) (hb : d241563 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d200199, d241563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200199, d241563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200200 q = 1) (hb : d241564 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d200200, d241564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200200, d241564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200201 q = 1) (hb : d241565 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d200201, d241565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200201, d241565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59383 (p : Pattern) (ha : d200207 p = 1) (hb : d241571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d198937 q = 1) (hb : d240587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d198937, d240587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59100 q ha hb
    | true =>
      simp only [d198937, d240587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59145 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199211 q = 1) (hb : d240806 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199211, d240806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199211, d240806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59197 q ha hb
  have h3 (q : Pattern) (ha : d199212 q = 1) (hb : d240807 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199212, d240807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d199212, d240807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199548 q = 1) (hb : d241057 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199548, d241057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199548, d241057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59258 q ha hb
  have h5 (q : Pattern) (ha : d199549 q = 1) (hb : d241058 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199549, d241058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199549, d241058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199550 q = 1) (hb : d241059 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199550, d241059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199550, d241059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199886 q = 1) (hb : d241313 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199886, d241313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199886, d241313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59321 q ha hb
  have h8 (q : Pattern) (ha : d199887 q = 1) (hb : d241314 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199887, d241314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199887, d241314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199888 q = 1) (hb : d241315 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199888, d241315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199888, d241315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199889 q = 1) (hb : d241316 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d199889, d241316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199889, d241316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200202 q = 1) (hb : d241566 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d200202, d241566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200202, d241566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59382 q ha hb
  have h12 (q : Pattern) (ha : d200203 q = 1) (hb : d241567 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d200203, d241567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200203, d241567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200204 q = 1) (hb : d241568 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d200204, d241568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200204, d241568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200205 q = 1) (hb : d241569 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d200205, d241569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200205, d241569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200206 q = 1) (hb : d241570 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d200206, d241570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200206, d241570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200207 q = 1) (hb : d241571 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d200207, d241571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200207, d241571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro59384 (p : Pattern) (ha : d200213 p = 1) (hb : d241577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200208 q = 1) (hb : d241572 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d200208, d241572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59383 q ha hb
    | true =>
      simp only [d200208, d241572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200209 q = 1) (hb : d241573 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d200209, d241573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200209, d241573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200210 q = 1) (hb : d241574 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d200210, d241574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200210, d241574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200211 q = 1) (hb : d241575 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d200211, d241575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200211, d241575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200212 q = 1) (hb : d241576 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d200212, d241576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200212, d241576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200213 q = 1) (hb : d241577 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d200213, d241577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200213, d241577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59385 (p : Pattern) (ha : d200219 p = 1) (hb : d241583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200214 q = 1) (hb : d241578 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d200214, d241578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59384 q ha hb
    | true =>
      simp only [d200214, d241578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200215 q = 1) (hb : d241579 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d200215, d241579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200215, d241579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200216 q = 1) (hb : d241580 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d200216, d241580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200216, d241580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200217 q = 1) (hb : d241581 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d200217, d241581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200217, d241581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200218 q = 1) (hb : d241582 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d200218, d241582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200218, d241582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200219 q = 1) (hb : d241583 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d200219, d241583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200219, d241583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59386 (p : Pattern) (ha : d200225 p = 1) (hb : d241589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200220 q = 1) (hb : d241584 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d200220, d241584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59385 q ha hb
    | true =>
      simp only [d200220, d241584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200221 q = 1) (hb : d241585 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d200221, d241585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200221, d241585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200222 q = 1) (hb : d241586 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d200222, d241586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200222, d241586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200223 q = 1) (hb : d241587 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d200223, d241587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200223, d241587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200224 q = 1) (hb : d241588 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d200224, d241588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200224, d241588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200225 q = 1) (hb : d241589 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d200225, d241589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200225, d241589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59387 (p : Pattern) (ha : d200231 p = 1) (hb : d241595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200226 q = 1) (hb : d241590 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d200226, d241590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59386 q ha hb
    | true =>
      simp only [d200226, d241590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200227 q = 1) (hb : d241591 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d200227, d241591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200227, d241591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200228 q = 1) (hb : d241592 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d200228, d241592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200228, d241592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200229 q = 1) (hb : d241593 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d200229, d241593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200229, d241593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200230 q = 1) (hb : d241594 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d200230, d241594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200230, d241594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200231 q = 1) (hb : d241595 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d200231, d241595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200231, d241595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59388 (p : Pattern) (ha : d200237 p = 1) (hb : d241601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200232 q = 1) (hb : d241596 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d200232, d241596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59387 q ha hb
    | true =>
      simp only [d200232, d241596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200233 q = 1) (hb : d241597 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d200233, d241597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200233, d241597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200234 q = 1) (hb : d241598 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d200234, d241598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200234, d241598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200235 q = 1) (hb : d241599 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d200235, d241599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200235, d241599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200236 q = 1) (hb : d241600 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d200236, d241600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200236, d241600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200237 q = 1) (hb : d241601 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d200237, d241601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200237, d241601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59389 (p : Pattern) (ha : d200243 p = 1) (hb : d241607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200238 q = 1) (hb : d241602 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d200238, d241602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59388 q ha hb
    | true =>
      simp only [d200238, d241602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200239 q = 1) (hb : d241603 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d200239, d241603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200239, d241603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200240 q = 1) (hb : d241604 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d200240, d241604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200240, d241604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200241 q = 1) (hb : d241605 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d200241, d241605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200241, d241605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200242 q = 1) (hb : d241606 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d200242, d241606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200242, d241606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200243 q = 1) (hb : d241607 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d200243, d241607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200243, d241607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59390 (p : Pattern) (ha : d200249 p = 1) (hb : d241613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200244 q = 1) (hb : d241608 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d200244, d241608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59389 q ha hb
    | true =>
      simp only [d200244, d241608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200245 q = 1) (hb : d241609 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d200245, d241609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200245, d241609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200246 q = 1) (hb : d241610 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d200246, d241610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200246, d241610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200247 q = 1) (hb : d241611 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d200247, d241611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200247, d241611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200248 q = 1) (hb : d241612 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d200248, d241612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200248, d241612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200249 q = 1) (hb : d241613 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d200249, d241613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200249, d241613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59391 (p : Pattern) (ha : d208034 p = 1) (hb : d231169 p = 1) : d241616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58763 q ha hb
    | true =>
      simp only [d23154, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23208 q = 1) (hb : d208034 q = 1) : d240285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23208, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23209 q = 1) (hb : d208034 q = 1) : d240286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23209, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23210 q = 1) (hb : d208034 q = 1) : d240287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23211 q = 1) (hb : d208034 q = 1) : d240288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231169 q = 1) : d241616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231169, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231169, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro59392 (p : Pattern) (ha : d208034 p = 1) (hb : d231179 p = 1) : d241626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208034 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d208034 q = 1) : d240261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58768 q ha hb
    | true =>
      simp only [d23184, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231175 q = 1) : d241622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231175, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231175, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231176 q = 1) : d241623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231176, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231176, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231177 q = 1) : d241624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231177, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231177, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231178 q = 1) : d241625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231178, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231178, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231179 q = 1) : d241626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231179, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231179, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59393 (p : Pattern) (ha : d208034 p = 1) (hb : d231185 p = 1) : d241632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d208034 q = 1) : d240290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58771 q ha hb
    | true =>
      simp only [d23213, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58772 q ha hb
  have h2 (q : Pattern) (ha : d23214 q = 1) (hb : d208034 q = 1) : d240291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231167 q = 1) : d241614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231167, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231167, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231168 q = 1) : d241615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231168, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231168, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231170 q = 1) : d241617 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231170, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231170, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59391 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231171 q = 1) : d241618 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231171, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231171, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231172 q = 1) : d241619 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231172, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231172, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d231173 q = 1) : d241620 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231173, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231173, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d231174 q = 1) : d241621 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231174, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231174, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d231180 q = 1) : d241627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231180, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231180, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59392 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d231181 q = 1) : d241628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231181, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231181, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d231182 q = 1) : d241629 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231182, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231182, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d231183 q = 1) : d241630 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231183, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231183, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d231184 q = 1) : d241631 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231184, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231184, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d231185 q = 1) : d241632 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231185, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231185, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59394 (p : Pattern) (ha : d208034 p = 1) (hb : d231191 p = 1) : d241638 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d208034 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231186 q = 1) : d241633 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231186, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231186, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59393 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231187 q = 1) : d241634 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231187, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231187, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231188 q = 1) : d241635 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231188, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231188, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231189 q = 1) : d241636 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231189, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231189, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231190 q = 1) : d241637 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231190, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231190, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231191 q = 1) : d241638 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231191, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231191, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro59395 (p : Pattern) (ha : d208034 p = 1) (hb : d231194 p = 1) : d241641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23393 q = 1) (hb : d208034 q = 1) : d240427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58800 q ha hb
    | true =>
      simp only [d23393, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58801 q ha hb
  have h2 (q : Pattern) (ha : d23394 q = 1) (hb : d208034 q = 1) : d240428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23394, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23395 q = 1) (hb : d208034 q = 1) : d240429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23395, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23396 q = 1) (hb : d208034 q = 1) : d240430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23397 q = 1) (hb : d208034 q = 1) : d240431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231194 q = 1) : d241641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231194, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231194, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro59396 (p : Pattern) (ha : d208034 p = 1) (hb : d231205 p = 1) : d241652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231200 q = 1) : d241647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231200, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58831 q hb ha
    | true =>
      simp only [d231200, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58807 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231201 q = 1) : d241648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231201, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231201, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231202 q = 1) : d241649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231202, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231202, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231203 q = 1) : d241650 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231203, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231203, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231204 q = 1) : d241651 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231204, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231204, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231205 q = 1) : d241652 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231205, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231205, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59397 (p : Pattern) (ha : d208034 p = 1) (hb : d231211 p = 1) : d241658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d208034 q = 1) : d240433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58799 q ha hb
    | true =>
      simp only [d23399, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58802 q ha hb
  have h2 (q : Pattern) (ha : d23400 q = 1) (hb : d208034 q = 1) : d240434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231192 q = 1) : d241639 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231192, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231192, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231193 q = 1) : d241640 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231193, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231193, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231195 q = 1) : d241642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231195, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231195, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59395 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231196 q = 1) : d241643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231196, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231196, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231197 q = 1) : d241644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231197, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231197, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d231198 q = 1) : d241645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231198, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231198, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d231199 q = 1) : d241646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231199, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231199, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d231206 q = 1) : d241653 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231206, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231206, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59396 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d231207 q = 1) : d241654 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231207, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231207, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d231208 q = 1) : d241655 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231208, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231208, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d231209 q = 1) : d241656 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231209, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231209, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d231210 q = 1) : d241657 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231210, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231210, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d231211 q = 1) : d241658 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231211, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231211, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59398 (p : Pattern) (ha : d208034 p = 1) (hb : d231217 p = 1) : d241664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231212 q = 1) : d241659 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231212, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231212, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59397 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231213 q = 1) : d241660 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231213, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231213, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231214 q = 1) : d241661 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231214, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231214, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231215 q = 1) : d241662 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231215, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231215, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231216 q = 1) : d241663 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231216, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231216, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231217 q = 1) : d241664 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231217, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231217, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59399 (p : Pattern) (ha : d208034 p = 1) (hb : d231221 p = 1) : d241668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23666 q = 1) (hb : d208034 q = 1) : d240625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58845 q ha hb
    | true =>
      simp only [d23666, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58846 q ha hb
  have h2 (q : Pattern) (ha : d23667 q = 1) (hb : d208034 q = 1) : d240626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23667, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23668 q = 1) (hb : d208034 q = 1) : d240627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23668, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23669 q = 1) (hb : d208034 q = 1) : d240628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23670 q = 1) (hb : d208034 q = 1) : d240629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231221 q = 1) : d241668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231221, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231221, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro59400 (p : Pattern) (ha : d208034 p = 1) (hb : d231232 p = 1) : d241679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231227 q = 1) : d241674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231227, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58879 q hb ha
    | true =>
      simp only [d231227, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58854 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231228 q = 1) : d241675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231228, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231228, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231229 q = 1) : d241676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231229, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231229, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231230 q = 1) : d241677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231230, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231230, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231231 q = 1) : d241678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231231, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231231, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231232 q = 1) : d241679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231232, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231232, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59401 (p : Pattern) (ha : d208034 p = 1) (hb : d231238 p = 1) : d241685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d208034 q = 1) : d240631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58844 q ha hb
    | true =>
      simp only [d23672, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58847 q ha hb
  have h2 (q : Pattern) (ha : d23673 q = 1) (hb : d208034 q = 1) : d240632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231219 q = 1) : d241666 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231219, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231219, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231220 q = 1) : d241667 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231220, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231220, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231222 q = 1) : d241669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231222, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231222, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59399 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231223 q = 1) : d241670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231223, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231223, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231224 q = 1) : d241671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231224, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231224, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d231225 q = 1) : d241672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231225, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231225, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d231226 q = 1) : d241673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231226, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231226, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d231233 q = 1) : d241680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231233, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231233, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59400 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d231234 q = 1) : d241681 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231234, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231234, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d231235 q = 1) : d241682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231235, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231235, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d231236 q = 1) : d241683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231236, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231236, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d231237 q = 1) : d241684 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231237, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231237, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d231238 q = 1) : d241685 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231238, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231238, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59402 (p : Pattern) (ha : d208034 p = 1) (hb : d231244 p = 1) : d241691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231239 q = 1) : d241686 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231239, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231239, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59401 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231240 q = 1) : d241687 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231240, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231240, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231241 q = 1) : d241688 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231241, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231241, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231242 q = 1) : d241689 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231242, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231242, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231243 q = 1) : d241690 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231243, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231243, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231244 q = 1) : d241691 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231244, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231244, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59403 (p : Pattern) (ha : d208034 p = 1) (hb : d231249 p = 1) : d241696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23988 q = 1) (hb : d208034 q = 1) : d240852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58895 q ha hb
    | true =>
      simp only [d23988, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58896 q ha hb
  have h2 (q : Pattern) (ha : d23989 q = 1) (hb : d208034 q = 1) : d240853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23989, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23990 q = 1) (hb : d208034 q = 1) : d240854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23990, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23991 q = 1) (hb : d208034 q = 1) : d240855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23992 q = 1) (hb : d208034 q = 1) : d240856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231249 q = 1) : d241696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231249, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231249, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro59404 (p : Pattern) (ha : d208034 p = 1) (hb : d231260 p = 1) : d241707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231255 q = 1) : d241702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231255, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58933 q hb ha
    | true =>
      simp only [d231255, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58904 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231256 q = 1) : d241703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231256, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231256, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231257 q = 1) : d241704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231257, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231257, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231258 q = 1) : d241705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231258, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231258, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231259 q = 1) : d241706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231259, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231259, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231260 q = 1) : d241707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231260, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231260, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59405 (p : Pattern) (ha : d208034 p = 1) (hb : d231266 p = 1) : d241713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23994 q = 1) (hb : d208034 q = 1) : d240858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58894 q ha hb
    | true =>
      simp only [d23994, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58897 q ha hb
  have h2 (q : Pattern) (ha : d23995 q = 1) (hb : d208034 q = 1) : d240859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23995, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231247 q = 1) : d241694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231247, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231247, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231248 q = 1) : d241695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231248, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231248, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231250 q = 1) : d241697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231250, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231250, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59403 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231251 q = 1) : d241698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231251, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231251, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231252 q = 1) : d241699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231252, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231252, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d231253 q = 1) : d241700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231253, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231253, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d231254 q = 1) : d241701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231254, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231254, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d231261 q = 1) : d241708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231261, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231261, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59404 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d231262 q = 1) : d241709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231262, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231262, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d231263 q = 1) : d241710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231263, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231263, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d231264 q = 1) : d241711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231264, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231264, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d231265 q = 1) : d241712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231265, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231265, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d231266 q = 1) : d241713 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231266, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231266, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59406 (p : Pattern) (ha : d208034 p = 1) (hb : d231272 p = 1) : d241719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231267 q = 1) : d241714 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231267, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231267, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59405 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231268 q = 1) : d241715 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231268, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231268, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231269 q = 1) : d241716 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231269, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231269, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231270 q = 1) : d241717 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231270, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231270, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231271 q = 1) : d241718 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231271, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231271, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231272 q = 1) : d241719 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231272, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231272, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59407 (p : Pattern) (ha : d208034 p = 1) (hb : d231278 p = 1) : d241725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24370 q = 1) (hb : d208034 q = 1) : d241104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58952 q ha hb
    | true =>
      simp only [d24370, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58953 q ha hb
  have h2 (q : Pattern) (ha : d24371 q = 1) (hb : d208034 q = 1) : d241105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24371, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24372 q = 1) (hb : d208034 q = 1) : d241106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24372, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24373 q = 1) (hb : d208034 q = 1) : d241107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24374 q = 1) (hb : d208034 q = 1) : d241108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231278 q = 1) : d241725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231278, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231278, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro59408 (p : Pattern) (ha : d208034 p = 1) (hb : d231289 p = 1) : d241736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231284 q = 1) : d241731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231284, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58990 q hb ha
    | true =>
      simp only [d231284, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58961 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231285 q = 1) : d241732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231285, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231285, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231286 q = 1) : d241733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231286, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231286, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231287 q = 1) : d241734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231287, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231287, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231288 q = 1) : d241735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231288, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231288, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231289 q = 1) : d241736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231289, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231289, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59409 (p : Pattern) (ha : d208034 p = 1) (hb : d231295 p = 1) : d241742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24376 q = 1) (hb : d208034 q = 1) : d241110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58951 q ha hb
    | true =>
      simp only [d24376, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58954 q ha hb
  have h2 (q : Pattern) (ha : d24377 q = 1) (hb : d208034 q = 1) : d241111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24377, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231276 q = 1) : d241723 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231276, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231276, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231277 q = 1) : d241724 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231277, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231277, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231279 q = 1) : d241726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231279, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231279, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59407 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231280 q = 1) : d241727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231280, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231280, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231281 q = 1) : d241728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231281, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231281, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d231282 q = 1) : d241729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231282, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231282, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d231283 q = 1) : d241730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231283, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231283, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d231290 q = 1) : d241737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231290, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231290, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59408 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d231291 q = 1) : d241738 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231291, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231291, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d231292 q = 1) : d241739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231292, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231292, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d231293 q = 1) : d241740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231293, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231293, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d231294 q = 1) : d241741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231294, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231294, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d231295 q = 1) : d241742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231295, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231295, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59410 (p : Pattern) (ha : d208034 p = 1) (hb : d231301 p = 1) : d241748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231296 q = 1) : d241743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231296, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231296, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59409 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231297 q = 1) : d241744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231297, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231297, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231298 q = 1) : d241745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231298, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231298, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231299 q = 1) : d241746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231299, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231299, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231300 q = 1) : d241747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231300, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231300, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231301 q = 1) : d241748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231301, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231301, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59411 (p : Pattern) (ha : d208034 p = 1) (hb : d231308 p = 1) : d241755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24751 q = 1) (hb : d208034 q = 1) : d241361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59009 q ha hb
    | true =>
      simp only [d24751, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59010 q ha hb
  have h2 (q : Pattern) (ha : d24752 q = 1) (hb : d208034 q = 1) : d241362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24752, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24753 q = 1) (hb : d208034 q = 1) : d241363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24753, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24754 q = 1) (hb : d208034 q = 1) : d241364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24755 q = 1) (hb : d208034 q = 1) : d241365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231308 q = 1) : d241755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231308, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231308, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro59412 (p : Pattern) (ha : d208034 p = 1) (hb : d231319 p = 1) : d241766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231314 q = 1) : d241761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231314, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59047 q hb ha
    | true =>
      simp only [d231314, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59018 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231315 q = 1) : d241762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231315, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231315, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231316 q = 1) : d241763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231316, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231316, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231317 q = 1) : d241764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231317, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231317, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231318 q = 1) : d241765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231318, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231318, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231319 q = 1) : d241766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231319, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231319, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59413 (p : Pattern) (ha : d208034 p = 1) (hb : d231325 p = 1) : d241772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24757 q = 1) (hb : d208034 q = 1) : d241367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59008 q ha hb
    | true =>
      simp only [d24757, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59011 q ha hb
  have h2 (q : Pattern) (ha : d24758 q = 1) (hb : d208034 q = 1) : d241368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24758, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231306 q = 1) : d241753 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231306, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d231306, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231307 q = 1) : d241754 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231307, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231307, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231309 q = 1) : d241756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231309, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231309, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59411 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231310 q = 1) : d241757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231310, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231310, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231311 q = 1) : d241758 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231311, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231311, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d231312 q = 1) : d241759 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231312, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231312, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d231313 q = 1) : d241760 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231313, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231313, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d231320 q = 1) : d241767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231320, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231320, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59412 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d231321 q = 1) : d241768 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231321, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231321, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d231322 q = 1) : d241769 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231322, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231322, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d231323 q = 1) : d241770 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231323, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231323, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d231324 q = 1) : d241771 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231324, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231324, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d231325 q = 1) : d241772 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231325, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231325, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro59414 (p : Pattern) (ha : d208034 p = 1) (hb : d231331 p = 1) : d241778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231326 q = 1) : d241773 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231326, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231326, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59413 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231327 q = 1) : d241774 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231327, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231327, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231328 q = 1) : d241775 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231328, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231328, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231329 q = 1) : d241776 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231329, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231329, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231330 q = 1) : d241777 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231330, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231330, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231331 q = 1) : d241778 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231331, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231331, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59415 (p : Pattern) (ha : d208034 p = 1) (hb : d231337 p = 1) : d241784 p = 1 := by
  have h0 (q : Pattern) (ha : d208034 q = 1) (hb : d231218 q = 1) : d241665 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231218, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59394 q ha hb
    | true =>
      simp only [d231218, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59398 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231245 q = 1) : d241692 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231245, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231245, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59402 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231246 q = 1) : d241693 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231246, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231246, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231273 q = 1) : d241720 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231273, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231273, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59406 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231274 q = 1) : d241721 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231274, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231274, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231275 q = 1) : d241722 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231275, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231275, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d231302 q = 1) : d241749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231302, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231302, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59410 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d231303 q = 1) : d241750 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231303, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231303, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d231304 q = 1) : d241751 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231304, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231304, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d231305 q = 1) : d241752 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d231305, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231305, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d231332 q = 1) : d241779 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231332, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231332, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59414 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d231333 q = 1) : d241780 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231333, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231333, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d231334 q = 1) : d241781 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231334, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231334, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d231335 q = 1) : d241782 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d231335, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d231335, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d231336 q = 1) : d241783 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d231336, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231336, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d231337 q = 1) : d241784 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d231337, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d231337, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro59416 (p : Pattern) (ha : d208034 p = 1) (hb : d231343 p = 1) : d241790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231338 q = 1) : d241785 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d231338, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59415 q ha hb
    | true =>
      simp only [d231338, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231339 q = 1) : d241786 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d231339, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231339, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231340 q = 1) : d241787 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d231340, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231340, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231341 q = 1) : d241788 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d231341, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231341, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231342 q = 1) : d241789 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d231342, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231342, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231343 q = 1) : d241790 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d231343, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231343, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59417 (p : Pattern) (ha : d208034 p = 1) (hb : d231349 p = 1) : d241796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231344 q = 1) : d241791 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d231344, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59416 q ha hb
    | true =>
      simp only [d231344, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231345 q = 1) : d241792 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d231345, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231345, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231346 q = 1) : d241793 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d231346, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231346, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231347 q = 1) : d241794 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d231347, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231347, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231348 q = 1) : d241795 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d231348, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231348, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231349 q = 1) : d241796 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d231349, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231349, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59418 (p : Pattern) (ha : d208034 p = 1) (hb : d231355 p = 1) : d241802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231350 q = 1) : d241797 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d231350, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59417 q ha hb
    | true =>
      simp only [d231350, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231351 q = 1) : d241798 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d231351, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231351, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231352 q = 1) : d241799 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d231352, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231352, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231353 q = 1) : d241800 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d231353, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231353, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231354 q = 1) : d241801 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d231354, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231354, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231355 q = 1) : d241802 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d231355, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231355, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59419 (p : Pattern) (ha : d208034 p = 1) (hb : d231361 p = 1) : d241808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231356 q = 1) : d241803 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d231356, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59418 q ha hb
    | true =>
      simp only [d231356, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231357 q = 1) : d241804 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d231357, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231357, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231358 q = 1) : d241805 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d231358, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231358, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231359 q = 1) : d241806 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d231359, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231359, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231360 q = 1) : d241807 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d231360, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231360, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231361 q = 1) : d241808 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d231361, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231361, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59420 (p : Pattern) (ha : d208034 p = 1) (hb : d231367 p = 1) : d241814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231362 q = 1) : d241809 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d231362, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59419 q ha hb
    | true =>
      simp only [d231362, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231363 q = 1) : d241810 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d231363, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231363, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231364 q = 1) : d241811 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d231364, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231364, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231365 q = 1) : d241812 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d231365, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231365, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231366 q = 1) : d241813 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d231366, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231366, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231367 q = 1) : d241814 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d231367, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231367, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59421 (p : Pattern) (ha : d208034 p = 1) (hb : d231373 p = 1) : d241820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231368 q = 1) : d241815 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d231368, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59420 q ha hb
    | true =>
      simp only [d231368, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231369 q = 1) : d241816 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d231369, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231369, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231370 q = 1) : d241817 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d231370, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231370, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231371 q = 1) : d241818 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d231371, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231371, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231372 q = 1) : d241819 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d231372, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231372, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231373 q = 1) : d241820 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d231373, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231373, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59422 (p : Pattern) (ha : d208034 p = 1) (hb : d231379 p = 1) : d241826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d231374 q = 1) : d241821 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d231374, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59421 q ha hb
    | true =>
      simp only [d231374, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d231375 q = 1) : d241822 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d231375, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231375, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d231376 q = 1) : d241823 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d231376, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231376, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d231377 q = 1) : d241824 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d231377, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231377, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d231378 q = 1) : d241825 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d231378, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231378, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d231379 q = 1) : d241826 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d231379, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231379, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59423 (p : Pattern) (ha : d198617 p = 1) (hb : d240282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198489 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198489, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59066 q ha hb
    | true =>
      simp only [d198489, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d198607 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198607, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198607, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198614 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198614, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198614, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198615 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198615, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198615, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198616 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198616, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198616, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198617 q = 1) (hb : d240282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198617, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198617, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59424 (p : Pattern) (ha : d198636 p = 1) (hb : d240289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198489 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198489, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59066 q ha hb
    | true =>
      simp only [d198489, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d198607 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198607, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198607, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d198614 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198614, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198614, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d198615 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198615, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198615, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198616 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198616, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198616, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198622 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198626 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198496 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198496, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59068 q ha hb
    | true =>
      simp only [d198496, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d198629 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198629, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d198629, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198633 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198633, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198633, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198634 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198634, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d198634, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198635 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198635, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d198635, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198636 q = 1) (hb : d240289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198636, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d198636, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59425 (p : Pattern) (ha : d198645 p = 1) (hb : d241616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198496 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198496, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59068 q ha hb
    | true =>
      simp only [d198496, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d198629 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198629, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198629, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198633 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198633, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198633, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198643 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198643, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198643, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198644 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198644, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198644, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198645 q = 1) (hb : d241616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198645, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198645, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59426 (p : Pattern) (ha : d198685 p = 1) (hb : d241626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198674 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198532 q = 1) (hb : d240261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198532, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59073 q ha hb
    | true =>
      simp only [d198532, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d198675 q = 1) (hb : d241622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198675, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198675, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198682 q = 1) (hb : d241623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198682, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198682, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198683 q = 1) (hb : d241624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198683, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198683, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198684 q = 1) (hb : d241625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198684, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198684, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198685 q = 1) (hb : d241626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198685, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198685, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59427 (p : Pattern) (ha : d198691 p = 1) (hb : d241632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198637 q = 1) (hb : d240290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198637, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59423 q ha hb
    | true =>
      simp only [d198637, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59424 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198640 q = 1) (hb : d240291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198640, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198640, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198641 q = 1) (hb : d241614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198641, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198641, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198642 q = 1) (hb : d241615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198642, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198642, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198646 q = 1) (hb : d241617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198646, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198646, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59425 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198647 q = 1) (hb : d241618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198647, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198647, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198648 q = 1) (hb : d241619 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198648, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198648, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198649 q = 1) (hb : d241620 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198649, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198649, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198650 q = 1) (hb : d241621 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198650, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198650, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198686 q = 1) (hb : d241627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198686, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198686, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59426 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198687 q = 1) (hb : d241628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198687, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198687, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198688 q = 1) (hb : d241629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198688, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198688, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198689 q = 1) (hb : d241630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198689, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198689, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198690 q = 1) (hb : d241631 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198690, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198690, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198691 q = 1) (hb : d241632 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198691, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198691, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59428 (p : Pattern) (ha : d198697 p = 1) (hb : d241638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d198544 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47793 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d198545 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d198546 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d198547 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d198548 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198692 q = 1) (hb : d241633 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198692, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198692, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59427 q ha hb
  have h8 (q : Pattern) (ha : d198693 q = 1) (hb : d241634 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198693, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198693, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198694 q = 1) (hb : d241635 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198694, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198694, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198695 q = 1) (hb : d241636 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198695, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198695, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198696 q = 1) (hb : d241637 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198696, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198696, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d198697 q = 1) (hb : d241638 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198697, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d198697, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro59429 (p : Pattern) (ha : d198808 p = 1) (hb : d240422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198715 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59103 q ha hb
    | true =>
      simp only [d198715, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59104 q ha hb
  have h5 (q : Pattern) (ha : d198798 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198798, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198805 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198805, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198806 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198806, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198807 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198807, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198808 q = 1) (hb : d240422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198808, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198808, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59430 (p : Pattern) (ha : d198829 p = 1) (hb : d240432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198715 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59103 q ha hb
    | true =>
      simp only [d198715, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59104 q ha hb
  have h4 (q : Pattern) (ha : d198798 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198798, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d198805 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198805, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d198806 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198806, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198807 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198807, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198814 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198819 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198725 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59106 q ha hb
    | true =>
      simp only [d198725, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59107 q ha hb
  have h13 (q : Pattern) (ha : d198822 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d198822, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198826 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198826, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198827 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198827, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d198827, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198828 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198828, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d198828, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198829 q = 1) (hb : d240432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198829, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d198829, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59431 (p : Pattern) (ha : d198849 p = 1) (hb : d241641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198725 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59106 q ha hb
    | true =>
      simp only [d198725, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59107 q ha hb
  have h3 (q : Pattern) (ha : d198822 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198822, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198826 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198826, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198847 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198847, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198847, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198848 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198848, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198848, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198849 q = 1) (hb : d241641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198849, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198849, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59432 (p : Pattern) (ha : d198917 p = 1) (hb : d241652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198906 q = 1) (hb : d241647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198906, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59139 q ha hb
    | true =>
      simp only [d198906, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59142 q ha hb
  have h3 (q : Pattern) (ha : d198907 q = 1) (hb : d241648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198907, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198907, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198913 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198914 q = 1) (hb : d241649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198914, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198914, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198915 q = 1) (hb : d241650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198915, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198915, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198916 q = 1) (hb : d241651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198916, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198916, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198917 q = 1) (hb : d241652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198917, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198917, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59433 (p : Pattern) (ha : d198930 p = 1) (hb : d241658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198830 q = 1) (hb : d240433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198830, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59429 q ha hb
    | true =>
      simp only [d198830, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59430 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198844 q = 1) (hb : d240434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198844, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198844, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198845 q = 1) (hb : d241639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198845, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198845, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198846 q = 1) (hb : d241640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198846, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198846, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198850 q = 1) (hb : d241642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198850, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198850, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59431 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d198852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198853 q = 1) (hb : d241643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198853, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198853, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198854 q = 1) (hb : d241644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198854, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198854, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198855 q = 1) (hb : d241645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198855, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198855, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198856 q = 1) (hb : d241646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198856, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198856, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198918 q = 1) (hb : d241653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198918, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198918, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59432 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198925 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198926 q = 1) (hb : d241654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198926, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198926, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198927 q = 1) (hb : d241655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198927, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198927, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198928 q = 1) (hb : d241656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198928, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198928, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198929 q = 1) (hb : d241657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198929, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198929, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198930 q = 1) (hb : d241658 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198930, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198930, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59434 (p : Pattern) (ha : d198936 p = 1) (hb : d241664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198931 q = 1) (hb : d241659 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198931, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198931, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59433 q ha hb
  have h2 (q : Pattern) (ha : d198932 q = 1) (hb : d241660 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198932, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198932, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198933 q = 1) (hb : d241661 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198933, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198933, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198934 q = 1) (hb : d241662 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198934, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198934, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198935 q = 1) (hb : d241663 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198935, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198935, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198936 q = 1) (hb : d241664 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198936, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198936, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59435 (p : Pattern) (ha : d199065 p = 1) (hb : d240620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198973 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59152 q ha hb
    | true =>
      simp only [d198973, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59153 q ha hb
  have h5 (q : Pattern) (ha : d199055 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199055, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199062 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199062, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199063 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199063, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199064 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199064, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199065 q = 1) (hb : d240620 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199065, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199065, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59436 (p : Pattern) (ha : d199086 p = 1) (hb : d240630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198973 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59152 q ha hb
    | true =>
      simp only [d198973, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59153 q ha hb
  have h4 (q : Pattern) (ha : d199055 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199055, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199062 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199062, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199063 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199063, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199064 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199064, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199071 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199076 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198983 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59155 q ha hb
    | true =>
      simp only [d198983, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59156 q ha hb
  have h13 (q : Pattern) (ha : d199079 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199079, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199083 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199083, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199084 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199084, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199084, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199085 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199085, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199085, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199086 q = 1) (hb : d240630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199086, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199086, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59437 (p : Pattern) (ha : d199106 p = 1) (hb : d241668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198983 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59155 q ha hb
    | true =>
      simp only [d198983, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59156 q ha hb
  have h3 (q : Pattern) (ha : d199079 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199079, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199083 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199083, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199104 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199104, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199104, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199105 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199105, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199105, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199106 q = 1) (hb : d241668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199106, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199106, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59438 (p : Pattern) (ha : d199191 p = 1) (hb : d241679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199180 q = 1) (hb : d241674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199180, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59191 q ha hb
    | true =>
      simp only [d199180, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59194 q ha hb
  have h3 (q : Pattern) (ha : d199181 q = 1) (hb : d241675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199181, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199181, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199187 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199188 q = 1) (hb : d241676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199188, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199188, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199189 q = 1) (hb : d241677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199189, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199189, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199190 q = 1) (hb : d241678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199190, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199190, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199191 q = 1) (hb : d241679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199191, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199191, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59439 (p : Pattern) (ha : d199204 p = 1) (hb : d241685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199087 q = 1) (hb : d240631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199087, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59435 q ha hb
    | true =>
      simp only [d199087, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59436 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199101 q = 1) (hb : d240632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199101, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199101, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199102 q = 1) (hb : d241666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199102, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199102, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199103 q = 1) (hb : d241667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199103, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199103, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199107 q = 1) (hb : d241669 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199107, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199107, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59437 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199109 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199110 q = 1) (hb : d241670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199110, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199110, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199111 q = 1) (hb : d241671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199111, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199111, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199112 q = 1) (hb : d241672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199112, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199112, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199113 q = 1) (hb : d241673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199113, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199113, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199192 q = 1) (hb : d241680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199192, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199192, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59438 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199200 q = 1) (hb : d241681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199200, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199200, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199201 q = 1) (hb : d241682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199201, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199201, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199202 q = 1) (hb : d241683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199202, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199202, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199203 q = 1) (hb : d241684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199203, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199203, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199204 q = 1) (hb : d241685 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199204, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199204, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59440 (p : Pattern) (ha : d199210 p = 1) (hb : d241691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199205 q = 1) (hb : d241686 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199205, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199205, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59439 q ha hb
  have h2 (q : Pattern) (ha : d199206 q = 1) (hb : d241687 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199206, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199206, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199207 q = 1) (hb : d241688 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199207, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199207, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199208 q = 1) (hb : d241689 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199208, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199208, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199209 q = 1) (hb : d241690 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199209, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199209, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199210 q = 1) (hb : d241691 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199210, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199210, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59441 (p : Pattern) (ha : d199376 p = 1) (hb : d240847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199283 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59209 q ha hb
    | true =>
      simp only [d199283, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59210 q ha hb
  have h5 (q : Pattern) (ha : d199357 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199357, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199373 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199373, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199374 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199374, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199375 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199375, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199376 q = 1) (hb : d240847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199376, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199376, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59442 (p : Pattern) (ha : d199397 p = 1) (hb : d240857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199283 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59209 q ha hb
    | true =>
      simp only [d199283, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59210 q ha hb
  have h4 (q : Pattern) (ha : d199357 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199357, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199373 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199373, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199374 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199374, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199375 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199375, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199293 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59212 q ha hb
    | true =>
      simp only [d199293, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59213 q ha hb
  have h13 (q : Pattern) (ha : d199390 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199390, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199394 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199394, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199395 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199395, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199395, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199396 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199396, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199396, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199397 q = 1) (hb : d240857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199397, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199397, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59443 (p : Pattern) (ha : d199417 p = 1) (hb : d241696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199293 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59212 q ha hb
    | true =>
      simp only [d199293, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59213 q ha hb
  have h3 (q : Pattern) (ha : d199390 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199390, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199394 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199394, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199415 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199415, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199415, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199416 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199416, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199416, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199417 q = 1) (hb : d241696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199417, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199417, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59444 (p : Pattern) (ha : d199528 p = 1) (hb : d241707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199508 q = 1) (hb : d241702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199508, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59250 q ha hb
    | true =>
      simp only [d199508, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59255 q ha hb
  have h3 (q : Pattern) (ha : d199509 q = 1) (hb : d241703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199509, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199509, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199525 q = 1) (hb : d241704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199525, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199525, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199526 q = 1) (hb : d241705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199526, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199526, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199527 q = 1) (hb : d241706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199527, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199527, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199528 q = 1) (hb : d241707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199528, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199528, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59445 (p : Pattern) (ha : d199541 p = 1) (hb : d241713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199301 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199398 q = 1) (hb : d240858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199398, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59441 q ha hb
    | true =>
      simp only [d199398, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59442 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199412 q = 1) (hb : d240859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199412, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199412, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199413 q = 1) (hb : d241694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199413, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199413, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199414 q = 1) (hb : d241695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199414, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199414, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199418 q = 1) (hb : d241697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199418, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199418, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59443 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199420 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199421 q = 1) (hb : d241698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199421, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199421, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199422 q = 1) (hb : d241699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199422, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199422, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199423 q = 1) (hb : d241700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199423, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199423, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199424 q = 1) (hb : d241701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199424, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199424, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199529 q = 1) (hb : d241708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199529, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199529, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59444 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199536 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199537 q = 1) (hb : d241709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199537, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199537, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199538 q = 1) (hb : d241710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199538, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199538, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199539 q = 1) (hb : d241711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199539, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199539, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199540 q = 1) (hb : d241712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199540, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199540, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199541 q = 1) (hb : d241713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199541, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199541, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59446 (p : Pattern) (ha : d199547 p = 1) (hb : d241719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199542 q = 1) (hb : d241714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199542, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199542, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59445 q ha hb
  have h2 (q : Pattern) (ha : d199543 q = 1) (hb : d241715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199543, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199543, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199544 q = 1) (hb : d241716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199544, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199544, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199545 q = 1) (hb : d241717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199545, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199545, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199546 q = 1) (hb : d241718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199546, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199546, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199547 q = 1) (hb : d241719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199547, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199547, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59447 (p : Pattern) (ha : d199712 p = 1) (hb : d241099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199617 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59270 q ha hb
    | true =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59271 q ha hb
  have h5 (q : Pattern) (ha : d199683 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199683, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199709 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199709, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199710 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199710, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199711 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199711, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199712 q = 1) (hb : d241099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199712, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199712, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59448 (p : Pattern) (ha : d199733 p = 1) (hb : d241109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199617 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59270 q ha hb
    | true =>
      simp only [d199617, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59271 q ha hb
  have h4 (q : Pattern) (ha : d199683 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199683, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199709 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199709, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199710 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199710, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199711 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199711, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199718 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199627 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59273 q ha hb
    | true =>
      simp only [d199627, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59274 q ha hb
  have h13 (q : Pattern) (ha : d199726 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199726, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199730 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199730, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199731 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199731, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199731, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199732 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199732, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199732, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199733 q = 1) (hb : d241109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199733, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199733, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59449 (p : Pattern) (ha : d199753 p = 1) (hb : d241725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199627 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59273 q ha hb
    | true =>
      simp only [d199627, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59274 q ha hb
  have h3 (q : Pattern) (ha : d199726 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199726, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199730 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199730, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199751 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199751, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199751, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199752 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199752, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199752, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199753 q = 1) (hb : d241725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199753, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199753, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59450 (p : Pattern) (ha : d199866 p = 1) (hb : d241736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199835 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199840 q = 1) (hb : d241731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199840, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59312 q ha hb
    | true =>
      simp only [d199840, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59318 q ha hb
  have h3 (q : Pattern) (ha : d199841 q = 1) (hb : d241732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199841, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199841, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199862 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199863 q = 1) (hb : d241733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199863, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199863, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199864 q = 1) (hb : d241734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199864, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199864, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199865 q = 1) (hb : d241735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199865, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199865, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199866 q = 1) (hb : d241736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199866, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199866, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59451 (p : Pattern) (ha : d199879 p = 1) (hb : d241742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199635 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199734 q = 1) (hb : d241110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199734, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59447 q ha hb
    | true =>
      simp only [d199734, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59448 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199748 q = 1) (hb : d241111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199748, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199748, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199749 q = 1) (hb : d241723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199749, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199749, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199750 q = 1) (hb : d241724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199750, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199750, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199754 q = 1) (hb : d241726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199754, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199754, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59449 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199756 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199757 q = 1) (hb : d241727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199757, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199757, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199758 q = 1) (hb : d241728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199758, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199758, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199759 q = 1) (hb : d241729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199759, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199759, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199760 q = 1) (hb : d241730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199760, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199760, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199867 q = 1) (hb : d241737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199867, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199867, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59450 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199874 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199875 q = 1) (hb : d241738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199875, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199875, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199876 q = 1) (hb : d241739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199876, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199876, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199877 q = 1) (hb : d241740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199877, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199877, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199878 q = 1) (hb : d241741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199878, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199878, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199879 q = 1) (hb : d241742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199879, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199879, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59452 (p : Pattern) (ha : d199885 p = 1) (hb : d241748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199880 q = 1) (hb : d241743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199880, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199880, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59451 q ha hb
  have h2 (q : Pattern) (ha : d199881 q = 1) (hb : d241744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199881, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199881, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199882 q = 1) (hb : d241745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199882, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199882, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199883 q = 1) (hb : d241746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199883, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199883, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199884 q = 1) (hb : d241747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199884, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199884, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199885 q = 1) (hb : d241748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199885, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199885, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59453 (p : Pattern) (ha : d200035 p = 1) (hb : d241356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199945 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59332 q ha hb
    | true =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59333 q ha hb
  have h5 (q : Pattern) (ha : d200000 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d200000, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200032 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200032, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d200033 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200033, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200034 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200034, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200035 q = 1) (hb : d241356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200035, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200035, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59454 (p : Pattern) (ha : d200056 p = 1) (hb : d241366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199945 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59332 q ha hb
    | true =>
      simp only [d199945, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59333 q ha hb
  have h4 (q : Pattern) (ha : d200000 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200000, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200032 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200032, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d200033 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200033, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200034 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200034, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d200041 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d200046 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199955 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59335 q ha hb
    | true =>
      simp only [d199955, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59336 q ha hb
  have h13 (q : Pattern) (ha : d200049 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d200049, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200053 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200053, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200054 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200054, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d200054, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200055 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200055, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d200055, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200056 q = 1) (hb : d241366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200056, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200056, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59455 (p : Pattern) (ha : d200076 p = 1) (hb : d241755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199955 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59335 q ha hb
    | true =>
      simp only [d199955, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59336 q ha hb
  have h3 (q : Pattern) (ha : d200049 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200049, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200053 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200053, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200074 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200074, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200074, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200075 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200075, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200075, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200076 q = 1) (hb : d241755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200076, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200076, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59456 (p : Pattern) (ha : d200182 p = 1) (hb : d241766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d200151 q = 1) (hb : d241761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200151, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59373 q ha hb
    | true =>
      simp only [d200151, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59379 q ha hb
  have h3 (q : Pattern) (ha : d200152 q = 1) (hb : d241762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200152, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200152, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200179 q = 1) (hb : d241763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200179, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200179, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200180 q = 1) (hb : d241764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200180, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200180, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200181 q = 1) (hb : d241765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200181, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200181, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200182 q = 1) (hb : d241766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200182, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200182, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59457 (p : Pattern) (ha : d200195 p = 1) (hb : d241772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199963 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200057 q = 1) (hb : d241367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200057, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59453 q ha hb
    | true =>
      simp only [d200057, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59454 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200071 q = 1) (hb : d241368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200071, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200071, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200072 q = 1) (hb : d241753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200072, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200072, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200073 q = 1) (hb : d241754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200073, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200073, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200077 q = 1) (hb : d241756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200077, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200077, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59455 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d200079 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d200080 q = 1) (hb : d241757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200080, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200080, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d200081 q = 1) (hb : d241758 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200081, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200081, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d200082 q = 1) (hb : d241759 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200082, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200082, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d200083 q = 1) (hb : d241760 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200083, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200083, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200183 q = 1) (hb : d241767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200183, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200183, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59456 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200190 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200191 q = 1) (hb : d241768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200191, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200191, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200192 q = 1) (hb : d241769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200192, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200192, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d200193 q = 1) (hb : d241770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200193, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200193, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d200194 q = 1) (hb : d241771 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200194, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d200194, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d200195 q = 1) (hb : d241772 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d200195, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200195, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59458 (p : Pattern) (ha : d200201 p = 1) (hb : d241778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200196 q = 1) (hb : d241773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d200196, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200196, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59457 q ha hb
  have h2 (q : Pattern) (ha : d200197 q = 1) (hb : d241774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d200197, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200197, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200198 q = 1) (hb : d241775 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d200198, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200198, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200199 q = 1) (hb : d241776 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d200199, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200199, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200200 q = 1) (hb : d241777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d200200, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200200, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200201 q = 1) (hb : d241778 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d200201, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200201, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59459 (p : Pattern) (ha : d200207 p = 1) (hb : d241784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d198937 q = 1) (hb : d241665 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d198937, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59428 q ha hb
    | true =>
      simp only [d198937, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59434 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199211 q = 1) (hb : d241692 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199211, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199211, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59440 q ha hb
  have h3 (q : Pattern) (ha : d199212 q = 1) (hb : d241693 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199212, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d199212, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199548 q = 1) (hb : d241720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199548, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199548, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59446 q ha hb
  have h5 (q : Pattern) (ha : d199549 q = 1) (hb : d241721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199549, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199549, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199550 q = 1) (hb : d241722 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199550, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199550, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199886 q = 1) (hb : d241749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199886, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199886, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59452 q ha hb
  have h8 (q : Pattern) (ha : d199887 q = 1) (hb : d241750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199887, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199887, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199888 q = 1) (hb : d241751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199888, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199888, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199889 q = 1) (hb : d241752 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d199889, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199889, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200202 q = 1) (hb : d241779 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d200202, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200202, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59458 q ha hb
  have h12 (q : Pattern) (ha : d200203 q = 1) (hb : d241780 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d200203, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200203, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200204 q = 1) (hb : d241781 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d200204, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200204, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200205 q = 1) (hb : d241782 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d200205, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200205, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200206 q = 1) (hb : d241783 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d200206, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200206, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200207 q = 1) (hb : d241784 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d200207, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200207, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro59460 (p : Pattern) (ha : d200213 p = 1) (hb : d241790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200208 q = 1) (hb : d241785 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d200208, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59459 q ha hb
    | true =>
      simp only [d200208, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200209 q = 1) (hb : d241786 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d200209, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200209, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200210 q = 1) (hb : d241787 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d200210, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200210, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200211 q = 1) (hb : d241788 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d200211, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200211, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200212 q = 1) (hb : d241789 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d200212, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200212, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200213 q = 1) (hb : d241790 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d200213, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200213, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59461 (p : Pattern) (ha : d200219 p = 1) (hb : d241796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200214 q = 1) (hb : d241791 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d200214, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59460 q ha hb
    | true =>
      simp only [d200214, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200215 q = 1) (hb : d241792 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d200215, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200215, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200216 q = 1) (hb : d241793 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d200216, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200216, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200217 q = 1) (hb : d241794 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d200217, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200217, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200218 q = 1) (hb : d241795 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d200218, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200218, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200219 q = 1) (hb : d241796 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d200219, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200219, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59462 (p : Pattern) (ha : d200225 p = 1) (hb : d241802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200220 q = 1) (hb : d241797 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d200220, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59461 q ha hb
    | true =>
      simp only [d200220, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200221 q = 1) (hb : d241798 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d200221, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200221, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200222 q = 1) (hb : d241799 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d200222, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200222, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200223 q = 1) (hb : d241800 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d200223, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200223, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200224 q = 1) (hb : d241801 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d200224, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200224, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200225 q = 1) (hb : d241802 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d200225, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200225, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59463 (p : Pattern) (ha : d200231 p = 1) (hb : d241808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200226 q = 1) (hb : d241803 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d200226, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59462 q ha hb
    | true =>
      simp only [d200226, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200227 q = 1) (hb : d241804 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d200227, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200227, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200228 q = 1) (hb : d241805 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d200228, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200228, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200229 q = 1) (hb : d241806 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d200229, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200229, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200230 q = 1) (hb : d241807 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d200230, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200230, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200231 q = 1) (hb : d241808 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d200231, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200231, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59464 (p : Pattern) (ha : d200237 p = 1) (hb : d241814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200232 q = 1) (hb : d241809 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d200232, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59463 q ha hb
    | true =>
      simp only [d200232, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200233 q = 1) (hb : d241810 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d200233, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200233, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200234 q = 1) (hb : d241811 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d200234, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200234, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200235 q = 1) (hb : d241812 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d200235, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200235, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200236 q = 1) (hb : d241813 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d200236, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200236, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200237 q = 1) (hb : d241814 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d200237, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200237, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59465 (p : Pattern) (ha : d200243 p = 1) (hb : d241820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200238 q = 1) (hb : d241815 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d200238, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59464 q ha hb
    | true =>
      simp only [d200238, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200239 q = 1) (hb : d241816 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d200239, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200239, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200240 q = 1) (hb : d241817 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d200240, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200240, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200241 q = 1) (hb : d241818 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d200241, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200241, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200242 q = 1) (hb : d241819 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d200242, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200242, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200243 q = 1) (hb : d241820 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d200243, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200243, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59466 (p : Pattern) (ha : d200249 p = 1) (hb : d241826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200244 q = 1) (hb : d241821 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d200244, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59465 q ha hb
    | true =>
      simp only [d200244, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200245 q = 1) (hb : d241822 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d200245, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200245, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200246 q = 1) (hb : d241823 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d200246, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200246, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200247 q = 1) (hb : d241824 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d200247, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200247, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200248 q = 1) (hb : d241825 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d200248, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200248, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200249 q = 1) (hb : d241826 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d200249, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200249, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro59467 (p : Pattern) (ha : d202015 p = 1) (hb : d240282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202011 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202011, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202012 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202012, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202013 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202013, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202014 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202014, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202015 q = 1) (hb : d240282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202015, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59468 (p : Pattern) (ha : d202020 p = 1) (hb : d240289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202011 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202011, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202012 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202012, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202013 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202013, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202014 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202014, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25282 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202016 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202016, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202017 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202017, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202018 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202018, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202019 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202019, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202020 q = 1) (hb : d240289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202020, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59469 (p : Pattern) (ha : d202027 p = 1) (hb : d241616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202016 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202016, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202017 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202017, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202025 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202025, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202026 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202026, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202027 q = 1) (hb : d241616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202027, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59470 (p : Pattern) (ha : d202037 p = 1) (hb : d241626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240261 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202033 q = 1) (hb : d241622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202033, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202034 q = 1) (hb : d241623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202034, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202035 q = 1) (hb : d241624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202035, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202036 q = 1) (hb : d241625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202036, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202037 q = 1) (hb : d241626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202037, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59471 (p : Pattern) (ha : d202043 p = 1) (hb : d241632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25197 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202021 q = 1) (hb : d240290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59467 q ha hb
    | true =>
      simp only [d202021, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59468 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202022 q = 1) (hb : d240291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202022, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202023 q = 1) (hb : d241614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202023, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202024 q = 1) (hb : d241615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202024, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202028 q = 1) (hb : d241617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202028, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59469 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202029 q = 1) (hb : d241618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202029, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202030 q = 1) (hb : d241619 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202030, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202031 q = 1) (hb : d241620 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202031, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202032 q = 1) (hb : d241621 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202032, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202038 q = 1) (hb : d241627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202038, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59470 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202039 q = 1) (hb : d241628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202039, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202040 q = 1) (hb : d241629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202040, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202041 q = 1) (hb : d241630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202041, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202042 q = 1) (hb : d241631 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202042, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202043 q = 1) (hb : d241632 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202043, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59472 (p : Pattern) (ha : d202049 p = 1) (hb : d241638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d202006 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47842 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d202007 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d202008 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d202009 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d202010 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202044 q = 1) (hb : d241633 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202044, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59471 q ha hb
  have h8 (q : Pattern) (ha : d202045 q = 1) (hb : d241634 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202045, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202046 q = 1) (hb : d241635 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202046, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202047 q = 1) (hb : d241636 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202047, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202048 q = 1) (hb : d241637 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202048, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202049 q = 1) (hb : d241638 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d202049, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro59473 (p : Pattern) (ha : d202054 p = 1) (hb : d240422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202050 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202050, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202051 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202051, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202052 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202052, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202053 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202053, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202054 q = 1) (hb : d240422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202054, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59474 (p : Pattern) (ha : d202059 p = 1) (hb : d240432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202050 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202050, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202051 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202051, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202052 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202052, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202053 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202053, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25531 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25536 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202055 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202055, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202056 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202056, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202057 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202057, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202058 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202058, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202059 q = 1) (hb : d240432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202059, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59475 (p : Pattern) (ha : d202066 p = 1) (hb : d241641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202055 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202055, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202056 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202056, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202064 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202064, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202065 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202065, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202066 q = 1) (hb : d241641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202066, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59476 (p : Pattern) (ha : d202076 p = 1) (hb : d241652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202072 q = 1) (hb : d241648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202072, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202072, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202073 q = 1) (hb : d241649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202073, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202073, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202074 q = 1) (hb : d241650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202074, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202074, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202075 q = 1) (hb : d241651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202075, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202075, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202076 q = 1) (hb : d241652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202076, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202076, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59477 (p : Pattern) (ha : d202082 p = 1) (hb : d241658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25410 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202060 q = 1) (hb : d240433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202060, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59473 q ha hb
    | true =>
      simp only [d202060, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59474 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202061 q = 1) (hb : d240434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202061, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202061, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202062 q = 1) (hb : d241639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202062, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202062, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202063 q = 1) (hb : d241640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202063, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202063, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202067 q = 1) (hb : d241642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202067, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202067, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59475 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25572 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202068 q = 1) (hb : d241643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202068, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202068, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202069 q = 1) (hb : d241644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202069, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202069, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202070 q = 1) (hb : d241645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202070, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202070, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202071 q = 1) (hb : d241646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202071, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202071, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202077 q = 1) (hb : d241653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202077, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202077, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59476 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202078 q = 1) (hb : d241654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202078, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202078, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202079 q = 1) (hb : d241655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202079, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202079, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202080 q = 1) (hb : d241656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202080, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202080, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202081 q = 1) (hb : d241657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202081, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202081, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202082 q = 1) (hb : d241658 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202082, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202082, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59478 (p : Pattern) (ha : d202088 p = 1) (hb : d241664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202083 q = 1) (hb : d241659 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202083, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202083, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59477 q ha hb
  have h2 (q : Pattern) (ha : d202084 q = 1) (hb : d241660 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202084, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202084, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202085 q = 1) (hb : d241661 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202085, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202085, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202086 q = 1) (hb : d241662 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202086, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202086, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202087 q = 1) (hb : d241663 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202087, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202087, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202088 q = 1) (hb : d241664 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202088, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202088, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59479 (p : Pattern) (ha : d202094 p = 1) (hb : d240620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202090 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202090, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202091 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202091, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202092 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202092, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202093 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202093, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202094 q = 1) (hb : d240620 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202094, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202094, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59480 (p : Pattern) (ha : d202099 p = 1) (hb : d240630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202090 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202090, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202091 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202091, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202092 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202092, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202093 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202093, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25892 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202095 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202095, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202096 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202096, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202097 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202097, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202097, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202098 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202098, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202098, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202099 q = 1) (hb : d240630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202099, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202099, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59481 (p : Pattern) (ha : d202106 p = 1) (hb : d241668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202095 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202095, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202096 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202096, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202104 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202104, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202104, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202105 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202105, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202105, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202106 q = 1) (hb : d241668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202106, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202106, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59482 (p : Pattern) (ha : d202116 p = 1) (hb : d241679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202112 q = 1) (hb : d241675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202112, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202112, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202113 q = 1) (hb : d241676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202113, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202113, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202114 q = 1) (hb : d241677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202114, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202114, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202115 q = 1) (hb : d241678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202115, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202115, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202116 q = 1) (hb : d241679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202116, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202116, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59483 (p : Pattern) (ha : d202122 p = 1) (hb : d241685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25743 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202100 q = 1) (hb : d240631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202100, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59479 q ha hb
    | true =>
      simp only [d202100, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59480 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202101 q = 1) (hb : d240632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202101, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202101, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202102 q = 1) (hb : d241666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202102, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202102, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202103 q = 1) (hb : d241667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202103, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202103, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202107 q = 1) (hb : d241669 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202107, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202107, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59481 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25928 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202108 q = 1) (hb : d241670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202108, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202108, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202109 q = 1) (hb : d241671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202109, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202109, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202110 q = 1) (hb : d241672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202110, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202110, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202111 q = 1) (hb : d241673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202111, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202111, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202117 q = 1) (hb : d241680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202117, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202117, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59482 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26065 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202118 q = 1) (hb : d241681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202118, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202118, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202119 q = 1) (hb : d241682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202119, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202119, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202120 q = 1) (hb : d241683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202120, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202120, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202121 q = 1) (hb : d241684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202121, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202121, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202122 q = 1) (hb : d241685 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202122, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202122, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59484 (p : Pattern) (ha : d202128 p = 1) (hb : d241691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202123 q = 1) (hb : d241686 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202123, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202123, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59483 q ha hb
  have h2 (q : Pattern) (ha : d202124 q = 1) (hb : d241687 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202124, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202124, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202125 q = 1) (hb : d241688 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202125, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202125, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202126 q = 1) (hb : d241689 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202126, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202126, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202127 q = 1) (hb : d241690 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202127, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202127, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202128 q = 1) (hb : d241691 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202128, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202128, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59485 (p : Pattern) (ha : d202135 p = 1) (hb : d240847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202131 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202131, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202132 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202132, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202133 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202133, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202134 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202134, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202135 q = 1) (hb : d240847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202135, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202135, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59486 (p : Pattern) (ha : d202140 p = 1) (hb : d240857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202131 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202131, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202132 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202132, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202133 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202133, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202134 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202134, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202136 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202136, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202137 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202137, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202138 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202138, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202138, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202139 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202139, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202139, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202140 q = 1) (hb : d240857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202140, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202140, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59487 (p : Pattern) (ha : d202147 p = 1) (hb : d241696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202136 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202136, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202137 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202137, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202145 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202145, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202145, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202146 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202146, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202146, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202147 q = 1) (hb : d241696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202147, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202147, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59488 (p : Pattern) (ha : d202157 p = 1) (hb : d241707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241702 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202153 q = 1) (hb : d241703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202153, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202153, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26519 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202154 q = 1) (hb : d241704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202154, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202154, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202155 q = 1) (hb : d241705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202155, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202155, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202156 q = 1) (hb : d241706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202156, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202156, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202157 q = 1) (hb : d241707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202157, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202157, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59489 (p : Pattern) (ha : d202163 p = 1) (hb : d241713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202141 q = 1) (hb : d240858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202141, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59485 q ha hb
    | true =>
      simp only [d202141, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59486 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202142 q = 1) (hb : d240859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202142, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202142, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202143 q = 1) (hb : d241694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202143, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202143, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202144 q = 1) (hb : d241695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202144, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202144, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202148 q = 1) (hb : d241697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202148, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202148, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59487 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26368 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202149 q = 1) (hb : d241698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202149, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202149, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202150 q = 1) (hb : d241699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202150, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202150, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202151 q = 1) (hb : d241700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202151, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202151, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202152 q = 1) (hb : d241701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202152, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202152, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202158 q = 1) (hb : d241708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202158, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202158, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59488 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26535 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202159 q = 1) (hb : d241709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202159, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202159, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202160 q = 1) (hb : d241710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202160, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202160, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202161 q = 1) (hb : d241711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202161, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202161, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202162 q = 1) (hb : d241712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202162, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202162, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202163 q = 1) (hb : d241713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202163, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202163, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59490 (p : Pattern) (ha : d202169 p = 1) (hb : d241719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202164 q = 1) (hb : d241714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202164, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202164, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59489 q ha hb
  have h2 (q : Pattern) (ha : d202165 q = 1) (hb : d241715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202165, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202165, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202166 q = 1) (hb : d241716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202166, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202166, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202167 q = 1) (hb : d241717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202167, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202167, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202168 q = 1) (hb : d241718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202168, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202168, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202169 q = 1) (hb : d241719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202169, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202169, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59491 (p : Pattern) (ha : d202177 p = 1) (hb : d241099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202173 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202173, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202174 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202174, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202175 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202175, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202176 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202176, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202177 q = 1) (hb : d241099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202177, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202177, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59492 (p : Pattern) (ha : d202182 p = 1) (hb : d241109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202173 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202173, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202174 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202174, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202175 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202175, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202176 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202176, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26793 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202178 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202178, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202179 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202179, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202180 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202180, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202180, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202181 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202181, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202181, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202182 q = 1) (hb : d241109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202182, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202182, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59493 (p : Pattern) (ha : d202189 p = 1) (hb : d241725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202178 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202178, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202179 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202179, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202187 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202187, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202187, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202188 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202188, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202188, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202189 q = 1) (hb : d241725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202189, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202189, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59494 (p : Pattern) (ha : d202199 p = 1) (hb : d241736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202195 q = 1) (hb : d241732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202195, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202195, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202196 q = 1) (hb : d241733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202196, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202196, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202197 q = 1) (hb : d241734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202197, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202197, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202198 q = 1) (hb : d241735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202198, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202198, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202199 q = 1) (hb : d241736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202199, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202199, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro59495 (p : Pattern) (ha : d202205 p = 1) (hb : d241742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26634 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202183 q = 1) (hb : d241110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202183, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59491 q ha hb
    | true =>
      simp only [d202183, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59492 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202184 q = 1) (hb : d241111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202184, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202184, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202185 q = 1) (hb : d241723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202185, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202185, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202186 q = 1) (hb : d241724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202186, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202186, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202190 q = 1) (hb : d241726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202190, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202190, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59493 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26829 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202191 q = 1) (hb : d241727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202191, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202191, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202192 q = 1) (hb : d241728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202192, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202192, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202193 q = 1) (hb : d241729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202193, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202193, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202194 q = 1) (hb : d241730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202194, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202194, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202200 q = 1) (hb : d241737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202200, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202200, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59494 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26998 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202201 q = 1) (hb : d241738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202201, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202201, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202202 q = 1) (hb : d241739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202202, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202202, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202203 q = 1) (hb : d241740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202203, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202203, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202204 q = 1) (hb : d241741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202204, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202204, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202205 q = 1) (hb : d241742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202205, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202205, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro59496 (p : Pattern) (ha : d202211 p = 1) (hb : d241748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202206 q = 1) (hb : d241743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202206, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202206, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59495 q ha hb
  have h2 (q : Pattern) (ha : d202207 q = 1) (hb : d241744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202207, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202207, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202208 q = 1) (hb : d241745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202208, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202208, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202209 q = 1) (hb : d241746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202209, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202209, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202210 q = 1) (hb : d241747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202210, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202210, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202211 q = 1) (hb : d241748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202211, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202211, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro59497 (p : Pattern) (ha : d202220 p = 1) (hb : d241356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202216 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202216, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202217 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202217, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202218 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202218, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202219 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202219, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202220 q = 1) (hb : d241356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202220, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202220, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro59498 (p : Pattern) (ha : d202225 p = 1) (hb : d241366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202216 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202216, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202217 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202217, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202218 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202218, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202219 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202219, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d27221 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27226 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202221 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202221, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202222 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202222, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202223 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202223, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202223, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202224 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202224, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202224, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202225 q = 1) (hb : d241366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202225, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202225, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro59499 (p : Pattern) (ha : d202232 p = 1) (hb : d241755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202221 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202221, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202222 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202222, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202230 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202230, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202230, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202231 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202231, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202231, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202232 q = 1) (hb : d241755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202232, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202232, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
