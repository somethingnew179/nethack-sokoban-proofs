import NetHack.Soko22Hazard87.AndIntroBlocks0088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro22250 (p : Pattern) (ha : d122965 p = 1) (hb : d124463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22248 q ha hb
    | true =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122964 q = 1) (hb : d124462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122964, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122964, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122965 q = 1) (hb : d124463 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122965, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122965, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22251 (p : Pattern) (ha : d122969 p = 1) (hb : d124467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122968 q = 1) (hb : d124466 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122968, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122968, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122969 q = 1) (hb : d124467 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122969, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122969, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22252 (p : Pattern) (ha : d122975 p = 1) (hb : d124473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122970 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22250 q ha hb
    | true =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
  have h2 (q : Pattern) (ha : d122971 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122971, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122971, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122972 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122972, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122972, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122973 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122973, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122973, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122974 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122974, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122974, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122975 q = 1) (hb : d124473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122975, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122975, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22253 (p : Pattern) (ha : d122978 p = 1) (hb : d124476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22248 q ha hb
    | true =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122964 q = 1) (hb : d124462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122964, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122964, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122978 q = 1) (hb : d124476 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122978, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122978, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22254 (p : Pattern) (ha : d122979 p = 1) (hb : d124477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122968 q = 1) (hb : d124466 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122968, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122968, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122979 q = 1) (hb : d124477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122979, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122979, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22255 (p : Pattern) (ha : d122985 p = 1) (hb : d124483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122970 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22250 q ha hb
    | true =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
  have h2 (q : Pattern) (ha : d122971 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122971, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122971, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122972 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122972, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122972, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122973 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122973, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122973, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122974 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122974, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122974, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122980 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22253 q ha hb
    | true =>
      simp only [d122980, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22254 q ha hb
  have h7 (q : Pattern) (ha : d122981 q = 1) (hb : d124479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122981, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122981, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122982 q = 1) (hb : d124480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122982, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122982, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122983 q = 1) (hb : d124481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122983, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122983, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122984 q = 1) (hb : d124482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122984, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122984, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122985 q = 1) (hb : d124483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122985, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122985, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22256 (p : Pattern) (ha : d122990 p = 1) (hb : d124488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22248 q ha hb
    | true =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122989 q = 1) (hb : d124487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122989, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122989, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122990 q = 1) (hb : d124488 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122990, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122990, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22257 (p : Pattern) (ha : d122992 p = 1) (hb : d124490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122991 q = 1) (hb : d124489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122991, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122991, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122992 q = 1) (hb : d124490 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122992, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122992, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22258 (p : Pattern) (ha : d122999 p = 1) (hb : d124497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22248 q ha hb
    | true =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122997 q = 1) (hb : d124495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122997, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122997, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122998 q = 1) (hb : d124496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122998, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122998, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122999 q = 1) (hb : d124497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122999, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122999, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22259 (p : Pattern) (ha : d123002 p = 1) (hb : d124500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123000 q = 1) (hb : d124498 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123000, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123000, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123001 q = 1) (hb : d124499 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123001, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123001, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123002 q = 1) (hb : d124500 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123002, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123002, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22260 (p : Pattern) (ha : d123010 p = 1) (hb : d124504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d52793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d52794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14835 q = 1) (hb : d123006 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14835, d123006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14835, d123006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123010 q = 1) (hb : d124504 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123010, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d123010, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22261 (p : Pattern) (ha : d123021 p = 1) (hb : d124510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123011 q = 1) (hb : d124505 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123011, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22260 q ha hb
    | true =>
      simp only [d123011, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22246 q ha hb
  have h2 (q : Pattern) (ha : d123012 q = 1) (hb : d124506 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123012, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123012, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123013 q = 1) (hb : d124507 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123013, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123013, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123018 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123019 q = 1) (hb : d124508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123019, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123019, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122938 q = 1) (hb : d124444 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22246 q ha hb
    | true =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
  have h7 (q : Pattern) (ha : d122939 q = 1) (hb : d124445 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122940 q = 1) (hb : d124446 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122947 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122948 q = 1) (hb : d124447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123020 q = 1) (hb : d124509 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123020, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123020, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123021 q = 1) (hb : d124510 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123021, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123021, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22262 (p : Pattern) (ha : d5023 p = 1) (hb : d122944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5019 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5020 q = 1) (hb : d69110 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d69111 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5021, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5023 q = 1) (hb : d122944 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5023, d122944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5023, d122944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22263 (p : Pattern) (ha : d123026 p = 1) (hb : d124518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122938 q = 1) (hb : d124444 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22246 q ha hb
    | true =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
  have h2 (q : Pattern) (ha : d122939 q = 1) (hb : d124445 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122940 q = 1) (hb : d124446 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122947 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122948 q = 1) (hb : d124447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122945 q = 1) (hb : d124513 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122945, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
    | true =>
      simp only [d122945, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22262 q hb ha
  have h7 (q : Pattern) (ha : d122946 q = 1) (hb : d124514 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122946, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122946, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122947 q = 1) (hb : d124515 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122947, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122947, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123024 q = 1) (hb : d124516 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123024, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123024, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123025 q = 1) (hb : d124517 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123025, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123025, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123026 q = 1) (hb : d124518 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123026, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123026, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22264 (p : Pattern) (ha : d123032 p = 1) (hb : d124524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123022 q = 1) (hb : d124511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123022, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22261 q ha hb
    | true =>
      simp only [d123022, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123023 q = 1) (hb : d124512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123023, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123023, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123027 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22263 q ha hb
    | true =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123028 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123029 q = 1) (hb : d124521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123029, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123029, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123030 q = 1) (hb : d124522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123030, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123030, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123031 q = 1) (hb : d124523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123031, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123031, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123032 q = 1) (hb : d124524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123032, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123032, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22265 (p : Pattern) (ha : d123036 p = 1) (hb : d124528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123027 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22263 q ha hb
    | true =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123028 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123033 q = 1) (hb : d124525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123033, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123033, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123034 q = 1) (hb : d124526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123034, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123034, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123035 q = 1) (hb : d124527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123035, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123035, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123036 q = 1) (hb : d124528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123036, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123036, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22266 (p : Pattern) (ha : d123044 p = 1) (hb : d124453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122938 q = 1) (hb : d124444 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22246 q ha hb
    | true =>
      simp only [d122938, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
  have h2 (q : Pattern) (ha : d122939 q = 1) (hb : d124445 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122940 q = 1) (hb : d124446 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122947 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122948 q = 1) (hb : d124447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122948, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123039 q = 1) (hb : d124448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123039, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22247 q ha hb
    | true =>
      simp only [d123039, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18634 q hb ha
  have h7 (q : Pattern) (ha : d123040 q = 1) (hb : d124449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123040, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123040, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123041 q = 1) (hb : d124450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123041, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123041, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123042 q = 1) (hb : d124451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123042, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123042, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123043 q = 1) (hb : d124452 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123043, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123043, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123044 q = 1) (hb : d124453 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123044, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123044, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22267 (p : Pattern) (ha : d123050 p = 1) (hb : d124534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123045 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123045, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22266 q ha hb
    | true =>
      simp only [d123045, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123046 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123046, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123046, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123047 q = 1) (hb : d124531 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123047, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123047, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123048 q = 1) (hb : d124532 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123048, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123048, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123049 q = 1) (hb : d124533 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123049, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123049, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123050 q = 1) (hb : d124534 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123050, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123050, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22268 (p : Pattern) (ha : d123056 p = 1) (hb : d124540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122993 q = 1) (hb : d124491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122993, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22256 q ha hb
    | true =>
      simp only [d122993, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22257 q ha hb
  have h2 (q : Pattern) (ha : d122994 q = 1) (hb : d124492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122994, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122994, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122995 q = 1) (hb : d124493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122995, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122995, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122996 q = 1) (hb : d124494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122996, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122996, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123003 q = 1) (hb : d124501 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123003, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22258 q ha hb
    | true =>
      simp only [d123003, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22259 q ha hb
  have h6 (q : Pattern) (ha : d123004 q = 1) (hb : d124502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123004, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123004, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123005 q = 1) (hb : d124503 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123005, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123005, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123037 q = 1) (hb : d124529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123037, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22264 q ha hb
    | true =>
      simp only [d123037, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22265 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122970 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123038 q = 1) (hb : d124530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123038, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123051 q = 1) (hb : d124535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123051, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22267 q ha hb
    | true =>
      simp only [d123051, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123052 q = 1) (hb : d124536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123052, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123052, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123053 q = 1) (hb : d124537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123053, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123054 q = 1) (hb : d124538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123054, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123055 q = 1) (hb : d124539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123055, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123056 q = 1) (hb : d124540 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123056, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123056, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22269 (p : Pattern) (ha : d123057 p = 1) (hb : d124541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22248 q ha hb
    | true =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122989 q = 1) (hb : d124487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122989, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122989, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123057 q = 1) (hb : d124541 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123057, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123057, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22270 (p : Pattern) (ha : d123058 p = 1) (hb : d124542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122991 q = 1) (hb : d124489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122991, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122991, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123058 q = 1) (hb : d124542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123058, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123058, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22271 (p : Pattern) (ha : d123063 p = 1) (hb : d124547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22248 q ha hb
    | true =>
      simp only [d122956, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122997 q = 1) (hb : d124495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122997, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122997, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122998 q = 1) (hb : d124496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122998, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122998, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123063 q = 1) (hb : d124547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123063, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123063, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22272 (p : Pattern) (ha : d123064 p = 1) (hb : d124548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123000 q = 1) (hb : d124498 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123000, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123000, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123001 q = 1) (hb : d124499 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123001, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123001, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123064 q = 1) (hb : d124548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123064, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123064, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22273 (p : Pattern) (ha : d123068 p = 1) (hb : d124552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123022 q = 1) (hb : d124511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123022, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22261 q ha hb
    | true =>
      simp only [d123022, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123023 q = 1) (hb : d124512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123023, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123023, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123027 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22263 q ha hb
    | true =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123028 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123029 q = 1) (hb : d124521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123029, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123029, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123030 q = 1) (hb : d124522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123030, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123030, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123031 q = 1) (hb : d124523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123031, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123031, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123068 q = 1) (hb : d124552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123068, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123068, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22274 (p : Pattern) (ha : d123069 p = 1) (hb : d124553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123027 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22263 q ha hb
    | true =>
      simp only [d123027, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123028 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22249 q ha hb
    | true =>
      simp only [d122960, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123033 q = 1) (hb : d124525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123033, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123033, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123034 q = 1) (hb : d124526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123034, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123034, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123035 q = 1) (hb : d124527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123035, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123035, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123069 q = 1) (hb : d124553 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123069, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123069, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22275 (p : Pattern) (ha : d123072 p = 1) (hb : d124556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123045 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123045, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22266 q ha hb
    | true =>
      simp only [d123045, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123046 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123046, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123046, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123047 q = 1) (hb : d124531 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123047, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123047, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123048 q = 1) (hb : d124532 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123048, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123048, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123049 q = 1) (hb : d124533 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123049, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123049, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123072 q = 1) (hb : d124556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123072, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123072, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22276 (p : Pattern) (ha : d123078 p = 1) (hb : d124562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122993 q = 1) (hb : d124491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122993, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22256 q ha hb
    | true =>
      simp only [d122993, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22257 q ha hb
  have h2 (q : Pattern) (ha : d122994 q = 1) (hb : d124492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122994, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122994, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122995 q = 1) (hb : d124493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122995, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122995, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122996 q = 1) (hb : d124494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122996, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122996, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123003 q = 1) (hb : d124501 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123003, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22258 q ha hb
    | true =>
      simp only [d123003, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22259 q ha hb
  have h6 (q : Pattern) (ha : d123004 q = 1) (hb : d124502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123004, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123004, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123005 q = 1) (hb : d124503 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123005, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123005, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123037 q = 1) (hb : d124529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123037, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22264 q ha hb
    | true =>
      simp only [d123037, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22265 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122970 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123038 q = 1) (hb : d124530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123038, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123051 q = 1) (hb : d124535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123051, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22267 q ha hb
    | true =>
      simp only [d123051, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123052 q = 1) (hb : d124536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123052, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123052, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123053 q = 1) (hb : d124537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123053, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123054 q = 1) (hb : d124538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123054, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123055 q = 1) (hb : d124539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123055, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123059 q = 1) (hb : d124543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123059, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22269 q ha hb
    | true =>
      simp only [d123059, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22270 q ha hb
  have h17 (q : Pattern) (ha : d123060 q = 1) (hb : d124544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123060, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123060, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123061 q = 1) (hb : d124545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123061, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123061, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d123062 q = 1) (hb : d124546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123062, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123062, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123065 q = 1) (hb : d124549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123065, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22271 q ha hb
    | true =>
      simp only [d123065, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22272 q ha hb
  have h21 (q : Pattern) (ha : d123066 q = 1) (hb : d124550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123066, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123066, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d123067 q = 1) (hb : d124551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123067, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123067, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123070 q = 1) (hb : d124554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123070, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22273 q ha hb
    | true =>
      simp only [d123070, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22274 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122980 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d123071 q = 1) (hb : d124555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d123071, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d123073 q = 1) (hb : d124557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123073, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22275 q ha hb
    | true =>
      simp only [d123073, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d123074 q = 1) (hb : d124558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123074, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d123074, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d123075 q = 1) (hb : d124559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d123075, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d123076 q = 1) (hb : d124560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123076, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d123076, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d123077 q = 1) (hb : d124561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123077, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123077, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d123078 q = 1) (hb : d124562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123078, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123078, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro22277 (p : Pattern) (ha : d123090 p = 1) (hb : d124574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123080 q = 1) (hb : d124564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123080, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22265 q ha hb
    | true =>
      simp only [d123080, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
  have h2 (q : Pattern) (ha : d123081 q = 1) (hb : d124565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123081, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123081, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123082 q = 1) (hb : d124566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123082, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123082, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123083 q = 1) (hb : d124567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123083, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123083, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123084 q = 1) (hb : d124568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123084, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123084, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123085 q = 1) (hb : d124569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123085, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
    | true =>
      simp only [d123085, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123086 q = 1) (hb : d124570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123086, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123086, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123087 q = 1) (hb : d124571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123087, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123087, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123088 q = 1) (hb : d124572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123088, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123088, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123089 q = 1) (hb : d124573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123089, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123089, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123090 q = 1) (hb : d124574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123090, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123090, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22278 (p : Pattern) (ha : d123096 p = 1) (hb : d124580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123085 q = 1) (hb : d124569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123085, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
    | true =>
      simp only [d123085, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123086 q = 1) (hb : d124570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123086, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123086, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123087 q = 1) (hb : d124571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123087, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123087, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123088 q = 1) (hb : d124572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123088, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123088, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123089 q = 1) (hb : d124573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123089, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123089, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123091 q = 1) (hb : d124575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123091, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22254 q ha hb
    | true =>
      simp only [d123091, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123092 q = 1) (hb : d124576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123092, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123092, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123093 q = 1) (hb : d124577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123093, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123093, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123094 q = 1) (hb : d124578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123094, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123094, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123095 q = 1) (hb : d124579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123095, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123095, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123096 q = 1) (hb : d124580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123096, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123096, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22279 (p : Pattern) (ha : d123103 p = 1) (hb : d124587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123070 q = 1) (hb : d124554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123070, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22273 q ha hb
    | true =>
      simp only [d123070, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22274 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123071 q = 1) (hb : d124555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123071, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123073 q = 1) (hb : d124557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123073, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22275 q ha hb
    | true =>
      simp only [d123073, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123074 q = 1) (hb : d124558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123074, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123074, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123075 q = 1) (hb : d124559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123075, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123101 q = 1) (hb : d124585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123101, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123101, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123102 q = 1) (hb : d124586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123102, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123102, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123103 q = 1) (hb : d124587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123103, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123103, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22280 (p : Pattern) (ha : d123105 p = 1) (hb : d124589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123091 q = 1) (hb : d124575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123091, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22254 q ha hb
    | true =>
      simp only [d123091, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123092 q = 1) (hb : d124576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123092, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123092, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123093 q = 1) (hb : d124577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123093, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123093, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123094 q = 1) (hb : d124578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123094, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123094, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123095 q = 1) (hb : d124579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123095, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123095, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123105 q = 1) (hb : d124589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123105, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123105, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22281 (p : Pattern) (ha : d123117 p = 1) (hb : d124595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14986 q = 1) (hb : d123111 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14986, d123111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14986, d123111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123116 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123117 q = 1) (hb : d124595 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123117, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123117, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22282 (p : Pattern) (ha : d123124 p = 1) (hb : d124596 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d14993 q = 1) (hb : d123118 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14993, d123118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14993, d123118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123123 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123124 q = 1) (hb : d124596 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123124, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123124, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22283 (p : Pattern) (ha : d123140 p = 1) (hb : d124601 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d15014 q = 1) (hb : d123139 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15014, d123139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15014, d123139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123133 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123140 q = 1) (hb : d124601 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123140, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123140, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22284 (p : Pattern) (ha : d123155 p = 1) (hb : d124607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123125 q = 1) (hb : d124597 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123125, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22281 q ha hb
    | true =>
      simp only [d123125, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22282 q ha hb
  have h2 (q : Pattern) (ha : d123126 q = 1) (hb : d124598 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123126, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123126, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123127 q = 1) (hb : d124599 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123127, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123127, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123138 q = 1) (hb : d124600 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123138, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123138, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123141 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22282 q ha hb
    | true =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
  have h7 (q : Pattern) (ha : d123142 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123143 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123152 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123153 q = 1) (hb : d124605 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123154 q = 1) (hb : d124606 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123154, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123154, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123155 q = 1) (hb : d124607 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123155, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123155, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22285 (p : Pattern) (ha : d6355 p = 1) (hb : d123149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d76090 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6351 q = 1) (hb : d76091 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6351, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5019 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6352 q = 1) (hb : d76092 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6352, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6353 q = 1) (hb : d76093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6353, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6354 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6354, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6355 q = 1) (hb : d123149 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6355, d123149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6355, d123149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22286 (p : Pattern) (ha : d123160 p = 1) (hb : d124615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123141 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22282 q ha hb
    | true =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
  have h2 (q : Pattern) (ha : d123142 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123143 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123153 q = 1) (hb : d124605 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123150 q = 1) (hb : d124610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123150, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
    | true =>
      simp only [d123150, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22285 q hb ha
  have h7 (q : Pattern) (ha : d123151 q = 1) (hb : d124611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123151, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123151, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123152 q = 1) (hb : d124612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123152, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123152, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123158 q = 1) (hb : d124613 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123158, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123158, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123159 q = 1) (hb : d124614 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123159, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123159, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123160 q = 1) (hb : d124615 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123160, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123160, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22287 (p : Pattern) (ha : d123166 p = 1) (hb : d124621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123156 q = 1) (hb : d124608 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123156, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22284 q ha hb
    | true =>
      simp only [d123156, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123157 q = 1) (hb : d124609 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123157, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123157, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123161 q = 1) (hb : d124616 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123161, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22286 q ha hb
    | true =>
      simp only [d123161, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123162 q = 1) (hb : d124617 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123162, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123162, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123163 q = 1) (hb : d124618 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123163, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123163, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123164 q = 1) (hb : d124619 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123164, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123164, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123165 q = 1) (hb : d124620 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123165, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123165, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123166 q = 1) (hb : d124621 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123166, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123166, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22288 (p : Pattern) (ha : d13190 p = 1) (hb : d123167 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d123167 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d123167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, d123167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22289 (p : Pattern) (ha : d123173 p = 1) (hb : d124627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123168 q = 1) (hb : d124622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123168, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
    | true =>
      simp only [d123168, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22288 q hb ha
  have h2 (q : Pattern) (ha : d123169 q = 1) (hb : d124623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123169, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123169, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123170 q = 1) (hb : d124624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123170, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123170, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123171 q = 1) (hb : d124625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123171, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123171, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123172 q = 1) (hb : d124626 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123172, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123172, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123173 q = 1) (hb : d124627 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123173, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123173, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22290 (p : Pattern) (ha : d123179 p = 1) (hb : d124633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123161 q = 1) (hb : d124616 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123161, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22286 q ha hb
    | true =>
      simp only [d123161, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123162 q = 1) (hb : d124617 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123162, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123162, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123174 q = 1) (hb : d124628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22289 q ha hb
    | true =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123175 q = 1) (hb : d124629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123176 q = 1) (hb : d124630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123176, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123176, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123177 q = 1) (hb : d124631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123177, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123177, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123178 q = 1) (hb : d124632 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123178, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123178, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123179 q = 1) (hb : d124633 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123179, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123179, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22291 (p : Pattern) (ha : d123200 p = 1) (hb : d124637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123141 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22282 q ha hb
    | true =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
  have h2 (q : Pattern) (ha : d123142 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123143 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123153 q = 1) (hb : d124605 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123195 q = 1) (hb : d124622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123195, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
    | true =>
      simp only [d123195, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18640 q hb ha
  have h7 (q : Pattern) (ha : d123196 q = 1) (hb : d124623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123196, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123196, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123197 q = 1) (hb : d124624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123197, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123197, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123198 q = 1) (hb : d124625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123198, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123198, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123199 q = 1) (hb : d124636 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123199, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123199, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123200 q = 1) (hb : d124637 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123200, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123200, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22292 (p : Pattern) (ha : d123206 p = 1) (hb : d124643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123201 q = 1) (hb : d124638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123201, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22291 q ha hb
    | true =>
      simp only [d123201, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123202 q = 1) (hb : d124639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123202, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123202, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123203 q = 1) (hb : d124640 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123203, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123203, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123204 q = 1) (hb : d124641 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123204, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123204, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123205 q = 1) (hb : d124642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123205, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123205, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123206 q = 1) (hb : d124643 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123206, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123206, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22293 (p : Pattern) (ha : d123212 p = 1) (hb : d124649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123180 q = 1) (hb : d124634 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123180, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22287 q ha hb
    | true =>
      simp only [d123180, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22290 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123193 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123194 q = 1) (hb : d124635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123194, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123194, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123207 q = 1) (hb : d124644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123207, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22292 q ha hb
    | true =>
      simp only [d123207, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123208 q = 1) (hb : d124645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123208, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123208, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123209 q = 1) (hb : d124646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123209, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123209, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123210 q = 1) (hb : d124647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123210, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123210, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123211 q = 1) (hb : d124648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123211, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123211, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123212 q = 1) (hb : d124649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123212, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123212, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22294 (p : Pattern) (ha : d123192 p = 1) (hb : d124654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123174 q = 1) (hb : d124628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22289 q ha hb
    | true =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123175 q = 1) (hb : d124629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123189 q = 1) (hb : d124651 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123189, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123189, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123190 q = 1) (hb : d124652 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123190, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123190, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123191 q = 1) (hb : d124653 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123191, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123191, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123192 q = 1) (hb : d124654 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123192, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123192, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22295 (p : Pattern) (ha : d123219 p = 1) (hb : d124660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123214 q = 1) (hb : d124655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123214, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22294 q ha hb
    | true =>
      simp only [d123214, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123215 q = 1) (hb : d124656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123215, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123215, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123216 q = 1) (hb : d124657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123216, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123216, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123217 q = 1) (hb : d124658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123217, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123217, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123218 q = 1) (hb : d124659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123218, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123218, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123219 q = 1) (hb : d124660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123219, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123219, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22296 (p : Pattern) (ha : d123225 p = 1) (hb : d124666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122976 q = 1) (hb : d124474 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122976, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122976, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22252 q ha hb
  have h2 (q : Pattern) (ha : d122977 q = 1) (hb : d124475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122977, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122977, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122986 q = 1) (hb : d124484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122986, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22252 q ha hb
    | true =>
      simp only [d122986, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22255 q ha hb
  have h4 (q : Pattern) (ha : d122987 q = 1) (hb : d124485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122987, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122987, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122988 q = 1) (hb : d124486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122988, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122988, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123079 q = 1) (hb : d124563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123079, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22268 q ha hb
    | true =>
      simp only [d123079, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22276 q ha hb
  have h7 (q : Pattern) (ha : d123097 q = 1) (hb : d124581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123097, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22277 q ha hb
    | true =>
      simp only [d123097, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22278 q ha hb
  have h8 (q : Pattern) (ha : d123098 q = 1) (hb : d124582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123098, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123098, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123099 q = 1) (hb : d124583 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123099, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123099, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123100 q = 1) (hb : d124584 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123100, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123100, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123104 q = 1) (hb : d124588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123104, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123104, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22279 q ha hb
  have h12 (q : Pattern) (ha : d123106 q = 1) (hb : d124590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123106, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123106, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22280 q ha hb
  have h13 (q : Pattern) (ha : d123107 q = 1) (hb : d124591 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123107, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123107, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123108 q = 1) (hb : d124592 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123108, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123108, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123109 q = 1) (hb : d124593 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123109, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d123109, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d123110 q = 1) (hb : d124594 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123110, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123110, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123213 q = 1) (hb : d124650 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123213, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123213, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22293 q ha hb
  have h18 (q : Pattern) (ha : d123220 q = 1) (hb : d124661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123220, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123220, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22295 q ha hb
  have h19 (q : Pattern) (ha : d123221 q = 1) (hb : d124662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123221, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123221, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123222 q = 1) (hb : d124663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123222, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123222, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d123223 q = 1) (hb : d124664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123223, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d123223, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d123224 q = 1) (hb : d124665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123224, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123224, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123225 q = 1) (hb : d124666 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123225, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123225, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22297 (p : Pattern) (ha : d123231 p = 1) (hb : d124672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123226 q = 1) (hb : d124667 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123226, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123226, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22296 q ha hb
  have h2 (q : Pattern) (ha : d123227 q = 1) (hb : d124668 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123227, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123227, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123228 q = 1) (hb : d124669 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123228, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123228, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123229 q = 1) (hb : d124670 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123229, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123229, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123230 q = 1) (hb : d124671 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123230, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123230, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123231 q = 1) (hb : d124672 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123231, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123231, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22298 (p : Pattern) (ha : d13287 p = 1) (hb : d123256 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13287 q = 1) (hb : d123256 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d123256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, d123256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22299 (p : Pattern) (ha : d123239 p = 1) (hb : d124676 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d15150 q = 1) (hb : d123235 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15150, d123235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15150, d123235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123238 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123239 q = 1) (hb : d124676 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123239, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d123239, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22300 (p : Pattern) (ha : d123244 p = 1) (hb : d124677 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d15155 q = 1) (hb : d123240 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15155, d123240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15155, d123240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123243 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123244 q = 1) (hb : d124677 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123244, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d123244, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22301 (p : Pattern) (ha : d123262 p = 1) (hb : d124687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123245 q = 1) (hb : d124678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22299 q ha hb
    | true =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
  have h2 (q : Pattern) (ha : d123246 q = 1) (hb : d124679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123247 q = 1) (hb : d124680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123254 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123255 q = 1) (hb : d124681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123257 q = 1) (hb : d124682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123257, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
    | true =>
      simp only [d123257, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22298 q hb ha
  have h7 (q : Pattern) (ha : d123258 q = 1) (hb : d124683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123258, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123258, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123259 q = 1) (hb : d124684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123259, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123259, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123260 q = 1) (hb : d124685 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123260, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123260, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123261 q = 1) (hb : d124686 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123261, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123261, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123262 q = 1) (hb : d124687 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123262, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123262, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22302 (p : Pattern) (ha : d123266 p = 1) (hb : d124691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123257 q = 1) (hb : d124682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123257, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
    | true =>
      simp only [d123257, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22298 q hb ha
  have h2 (q : Pattern) (ha : d123258 q = 1) (hb : d124683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123258, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123258, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123259 q = 1) (hb : d124684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123259, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123259, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123260 q = 1) (hb : d124685 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123260, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123260, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123265 q = 1) (hb : d124690 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123265, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123265, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123266 q = 1) (hb : d124691 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123266, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123266, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22303 (p : Pattern) (ha : d123272 p = 1) (hb : d124697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22301 q ha hb
    | true =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123271 q = 1) (hb : d124696 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123271, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123271, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123272 q = 1) (hb : d124697 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123272, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123272, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22304 (p : Pattern) (ha : d123276 p = 1) (hb : d124701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123275 q = 1) (hb : d124700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123275, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123275, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123276 q = 1) (hb : d124701 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123276, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123276, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22305 (p : Pattern) (ha : d123282 p = 1) (hb : d124707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123277 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22303 q ha hb
    | true =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
  have h2 (q : Pattern) (ha : d123278 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123278, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123278, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123279 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123279, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123279, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123280 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123280, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123280, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123281 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123281, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123281, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123282 q = 1) (hb : d124707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123282, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123282, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22306 (p : Pattern) (ha : d123285 p = 1) (hb : d124710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22301 q ha hb
    | true =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123271 q = 1) (hb : d124696 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123271, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123271, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123285 q = 1) (hb : d124710 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123285, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123285, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22307 (p : Pattern) (ha : d123286 p = 1) (hb : d124711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123275 q = 1) (hb : d124700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123275, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123275, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123286 q = 1) (hb : d124711 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123286, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123286, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22308 (p : Pattern) (ha : d123292 p = 1) (hb : d124717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123277 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22303 q ha hb
    | true =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
  have h2 (q : Pattern) (ha : d123278 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123278, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123278, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123279 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123279, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123279, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123280 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123280, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123280, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123281 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123281, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123281, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123287 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22306 q ha hb
    | true =>
      simp only [d123287, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22307 q ha hb
  have h7 (q : Pattern) (ha : d123288 q = 1) (hb : d124713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123288, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123288, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123289 q = 1) (hb : d124714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123289, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123289, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123290 q = 1) (hb : d124715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123290, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123290, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123291 q = 1) (hb : d124716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123291, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123291, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123292 q = 1) (hb : d124717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123292, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123292, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22309 (p : Pattern) (ha : d123297 p = 1) (hb : d124722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22301 q ha hb
    | true =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123296 q = 1) (hb : d124721 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123296, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123296, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123297 q = 1) (hb : d124722 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123297, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123297, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22310 (p : Pattern) (ha : d123299 p = 1) (hb : d124724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123298 q = 1) (hb : d124723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123298, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123298, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123299 q = 1) (hb : d124724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123299, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123299, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22311 (p : Pattern) (ha : d123306 p = 1) (hb : d124731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22301 q ha hb
    | true =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123304 q = 1) (hb : d124729 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123304, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123304, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123305 q = 1) (hb : d124730 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123305, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123305, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123306 q = 1) (hb : d124731 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123306, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123306, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22312 (p : Pattern) (ha : d123309 p = 1) (hb : d124734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123307 q = 1) (hb : d124732 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123307, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123307, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123308 q = 1) (hb : d124733 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123308, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123308, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123309 q = 1) (hb : d124734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123309, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123309, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22313 (p : Pattern) (ha : d123317 p = 1) (hb : d124738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15228 q = 1) (hb : d123313 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15228, d123313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15228, d123313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123316 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123317 q = 1) (hb : d124738 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123317, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d123317, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22314 (p : Pattern) (ha : d123328 p = 1) (hb : d124744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123318 q = 1) (hb : d124739 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123318, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22313 q ha hb
    | true =>
      simp only [d123318, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22299 q ha hb
  have h2 (q : Pattern) (ha : d123319 q = 1) (hb : d124740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123319, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123319, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123320 q = 1) (hb : d124741 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123320, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123320, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123325 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123326 q = 1) (hb : d124742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123326, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123326, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123245 q = 1) (hb : d124678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22299 q ha hb
    | true =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
  have h7 (q : Pattern) (ha : d123246 q = 1) (hb : d124679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123247 q = 1) (hb : d124680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123254 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123255 q = 1) (hb : d124681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123327 q = 1) (hb : d124743 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123327, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123327, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123328 q = 1) (hb : d124744 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123328, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123328, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22315 (p : Pattern) (ha : d5139 p = 1) (hb : d123251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5135 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5136 q = 1) (hb : d69223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d69224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5137, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5139 q = 1) (hb : d123251 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5139, d123251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5139, d123251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22316 (p : Pattern) (ha : d123333 p = 1) (hb : d124752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123245 q = 1) (hb : d124678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22299 q ha hb
    | true =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
  have h2 (q : Pattern) (ha : d123246 q = 1) (hb : d124679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123247 q = 1) (hb : d124680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123254 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123255 q = 1) (hb : d124681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123252 q = 1) (hb : d124747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123252, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
    | true =>
      simp only [d123252, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22315 q hb ha
  have h7 (q : Pattern) (ha : d123253 q = 1) (hb : d124748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123253, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123253, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123254 q = 1) (hb : d124749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123254, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123254, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123331 q = 1) (hb : d124750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123331, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123331, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123332 q = 1) (hb : d124751 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123332, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123332, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123333 q = 1) (hb : d124752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123333, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123333, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22317 (p : Pattern) (ha : d123339 p = 1) (hb : d124758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123329 q = 1) (hb : d124745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123329, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22314 q ha hb
    | true =>
      simp only [d123329, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123330 q = 1) (hb : d124746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123330, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123330, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123334 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22316 q ha hb
    | true =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123335 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123336 q = 1) (hb : d124755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123336, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123336, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123337 q = 1) (hb : d124756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123337, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123337, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123338 q = 1) (hb : d124757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123338, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123338, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123339 q = 1) (hb : d124758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123339, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123339, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22318 (p : Pattern) (ha : d123343 p = 1) (hb : d124762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123334 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22316 q ha hb
    | true =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123335 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123340 q = 1) (hb : d124759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123340, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123340, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123341 q = 1) (hb : d124760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123341, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123341, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123342 q = 1) (hb : d124761 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123342, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123342, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123343 q = 1) (hb : d124762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123343, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123343, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22319 (p : Pattern) (ha : d123351 p = 1) (hb : d124687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123245 q = 1) (hb : d124678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22299 q ha hb
    | true =>
      simp only [d123245, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
  have h2 (q : Pattern) (ha : d123246 q = 1) (hb : d124679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123247 q = 1) (hb : d124680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123254 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123255 q = 1) (hb : d124681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123255, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123346 q = 1) (hb : d124682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123346, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22300 q ha hb
    | true =>
      simp only [d123346, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18682 q hb ha
  have h7 (q : Pattern) (ha : d123347 q = 1) (hb : d124683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123347, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123347, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123348 q = 1) (hb : d124684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123348, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123348, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123349 q = 1) (hb : d124685 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123349, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123349, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123350 q = 1) (hb : d124686 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123350, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123350, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123351 q = 1) (hb : d124687 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123351, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123351, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22320 (p : Pattern) (ha : d123357 p = 1) (hb : d124768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123352 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123352, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22319 q ha hb
    | true =>
      simp only [d123352, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123353 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123353, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123353, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123354 q = 1) (hb : d124765 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123354, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123354, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123355 q = 1) (hb : d124766 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123355, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123355, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123356 q = 1) (hb : d124767 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123356, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123356, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123357 q = 1) (hb : d124768 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123357, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123357, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22321 (p : Pattern) (ha : d123363 p = 1) (hb : d124774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123300 q = 1) (hb : d124725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123300, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22309 q ha hb
    | true =>
      simp only [d123300, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22310 q ha hb
  have h2 (q : Pattern) (ha : d123301 q = 1) (hb : d124726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123301, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123301, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123302 q = 1) (hb : d124727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123302, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123302, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123303 q = 1) (hb : d124728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123303, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123303, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123310 q = 1) (hb : d124735 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123310, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22311 q ha hb
    | true =>
      simp only [d123310, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22312 q ha hb
  have h6 (q : Pattern) (ha : d123311 q = 1) (hb : d124736 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123311, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123311, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123312 q = 1) (hb : d124737 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123312, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123312, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123344 q = 1) (hb : d124763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123344, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22317 q ha hb
    | true =>
      simp only [d123344, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22318 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123277 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123345 q = 1) (hb : d124764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123345, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123358 q = 1) (hb : d124769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123358, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22320 q ha hb
    | true =>
      simp only [d123358, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123359 q = 1) (hb : d124770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123359, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123359, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123360 q = 1) (hb : d124771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123360, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123361 q = 1) (hb : d124772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123361, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123362 q = 1) (hb : d124773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123362, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123363 q = 1) (hb : d124774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123363, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123363, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22322 (p : Pattern) (ha : d123364 p = 1) (hb : d124775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22301 q ha hb
    | true =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123296 q = 1) (hb : d124721 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123296, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123296, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123364 q = 1) (hb : d124775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123364, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123364, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22323 (p : Pattern) (ha : d123365 p = 1) (hb : d124776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123298 q = 1) (hb : d124723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123298, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123298, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123365 q = 1) (hb : d124776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123365, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123365, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22324 (p : Pattern) (ha : d123370 p = 1) (hb : d124781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22301 q ha hb
    | true =>
      simp only [d123263, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123304 q = 1) (hb : d124729 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123304, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123304, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123305 q = 1) (hb : d124730 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123305, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123305, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123370 q = 1) (hb : d124781 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123370, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123370, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22325 (p : Pattern) (ha : d123371 p = 1) (hb : d124782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123307 q = 1) (hb : d124732 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123307, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123307, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123308 q = 1) (hb : d124733 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123308, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123308, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123371 q = 1) (hb : d124782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123371, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123371, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22326 (p : Pattern) (ha : d123375 p = 1) (hb : d124786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123329 q = 1) (hb : d124745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123329, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22314 q ha hb
    | true =>
      simp only [d123329, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123330 q = 1) (hb : d124746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123330, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123330, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123334 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22316 q ha hb
    | true =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123335 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123336 q = 1) (hb : d124755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123336, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123336, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123337 q = 1) (hb : d124756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123337, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123337, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123338 q = 1) (hb : d124757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123338, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123338, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123375 q = 1) (hb : d124786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123375, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123375, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22327 (p : Pattern) (ha : d123376 p = 1) (hb : d124787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123334 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22316 q ha hb
    | true =>
      simp only [d123334, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123335 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22302 q ha hb
    | true =>
      simp only [d123267, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123340 q = 1) (hb : d124759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123340, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123340, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123341 q = 1) (hb : d124760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123341, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123341, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123342 q = 1) (hb : d124761 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123342, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123342, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123376 q = 1) (hb : d124787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123376, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123376, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22328 (p : Pattern) (ha : d123379 p = 1) (hb : d124790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123352 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123352, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22319 q ha hb
    | true =>
      simp only [d123352, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123353 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123353, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123353, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123354 q = 1) (hb : d124765 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123354, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123354, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123355 q = 1) (hb : d124766 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123355, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123355, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123356 q = 1) (hb : d124767 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123356, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123356, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123379 q = 1) (hb : d124790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123379, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123379, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22329 (p : Pattern) (ha : d123385 p = 1) (hb : d124796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123300 q = 1) (hb : d124725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123300, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22309 q ha hb
    | true =>
      simp only [d123300, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22310 q ha hb
  have h2 (q : Pattern) (ha : d123301 q = 1) (hb : d124726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123301, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123301, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123302 q = 1) (hb : d124727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123302, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123302, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123303 q = 1) (hb : d124728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123303, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123303, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123310 q = 1) (hb : d124735 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123310, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22311 q ha hb
    | true =>
      simp only [d123310, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22312 q ha hb
  have h6 (q : Pattern) (ha : d123311 q = 1) (hb : d124736 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123311, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123311, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123312 q = 1) (hb : d124737 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123312, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123312, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123344 q = 1) (hb : d124763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123344, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22317 q ha hb
    | true =>
      simp only [d123344, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22318 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123277 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123345 q = 1) (hb : d124764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123345, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123358 q = 1) (hb : d124769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123358, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22320 q ha hb
    | true =>
      simp only [d123358, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123359 q = 1) (hb : d124770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123359, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123359, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123360 q = 1) (hb : d124771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123360, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123361 q = 1) (hb : d124772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123361, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123362 q = 1) (hb : d124773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123362, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123366 q = 1) (hb : d124777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123366, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22322 q ha hb
    | true =>
      simp only [d123366, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22323 q ha hb
  have h17 (q : Pattern) (ha : d123367 q = 1) (hb : d124778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123367, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123367, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123368 q = 1) (hb : d124779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123368, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123368, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d123369 q = 1) (hb : d124780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123369, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123369, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123372 q = 1) (hb : d124783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123372, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22324 q ha hb
    | true =>
      simp only [d123372, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22325 q ha hb
  have h21 (q : Pattern) (ha : d123373 q = 1) (hb : d124784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123373, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123373, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d123374 q = 1) (hb : d124785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123374, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123374, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123377 q = 1) (hb : d124788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123377, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22326 q ha hb
    | true =>
      simp only [d123377, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22327 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d123287 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d123378 q = 1) (hb : d124789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d123378, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d123380 q = 1) (hb : d124791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123380, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22328 q ha hb
    | true =>
      simp only [d123380, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d123381 q = 1) (hb : d124792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123381, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d123381, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d123382 q = 1) (hb : d124793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d123382, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d123383 q = 1) (hb : d124794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123383, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d123383, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d123384 q = 1) (hb : d124795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123384, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123384, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d123385 q = 1) (hb : d124796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123385, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123385, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro22330 (p : Pattern) (ha : d123397 p = 1) (hb : d124808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123387 q = 1) (hb : d124798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123387, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22318 q ha hb
    | true =>
      simp only [d123387, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
  have h2 (q : Pattern) (ha : d123388 q = 1) (hb : d124799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123388, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123388, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123389 q = 1) (hb : d124800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123389, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123389, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123390 q = 1) (hb : d124801 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123390, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123390, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123391 q = 1) (hb : d124802 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123391, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123391, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123392 q = 1) (hb : d124803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123392, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
    | true =>
      simp only [d123392, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123393 q = 1) (hb : d124804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123393, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123393, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123394 q = 1) (hb : d124805 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123394, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123394, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123395 q = 1) (hb : d124806 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123395, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123395, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123396 q = 1) (hb : d124807 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123396, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123396, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123397 q = 1) (hb : d124808 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123397, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123397, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22331 (p : Pattern) (ha : d123403 p = 1) (hb : d124814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123392 q = 1) (hb : d124803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123392, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
    | true =>
      simp only [d123392, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123393 q = 1) (hb : d124804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123393, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123393, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123394 q = 1) (hb : d124805 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123394, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123394, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123395 q = 1) (hb : d124806 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123395, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123395, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123396 q = 1) (hb : d124807 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123396, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123396, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123398 q = 1) (hb : d124809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123398, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22307 q ha hb
    | true =>
      simp only [d123398, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123399 q = 1) (hb : d124810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123399, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123399, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123400 q = 1) (hb : d124811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123400, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123400, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123401 q = 1) (hb : d124812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123401, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123401, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123402 q = 1) (hb : d124813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123402, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123402, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123403 q = 1) (hb : d124814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123403, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123403, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22332 (p : Pattern) (ha : d123410 p = 1) (hb : d124821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123377 q = 1) (hb : d124788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123377, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22326 q ha hb
    | true =>
      simp only [d123377, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22327 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123287 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123378 q = 1) (hb : d124789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123378, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123380 q = 1) (hb : d124791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123380, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22328 q ha hb
    | true =>
      simp only [d123380, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123381 q = 1) (hb : d124792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123381, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123381, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123382 q = 1) (hb : d124793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123382, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123408 q = 1) (hb : d124819 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123408, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123408, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123409 q = 1) (hb : d124820 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123409, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123409, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123410 q = 1) (hb : d124821 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123410, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123410, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22333 (p : Pattern) (ha : d123412 p = 1) (hb : d124823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123398 q = 1) (hb : d124809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123398, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22307 q ha hb
    | true =>
      simp only [d123398, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123399 q = 1) (hb : d124810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123399, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123399, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123400 q = 1) (hb : d124811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123400, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123400, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123401 q = 1) (hb : d124812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123401, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123401, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123402 q = 1) (hb : d124813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123402, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123402, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123412 q = 1) (hb : d124823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123412, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123412, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22334 (p : Pattern) (ha : d123424 p = 1) (hb : d124829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15379 q = 1) (hb : d123418 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15379, d123418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15379, d123418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123423 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123424 q = 1) (hb : d124829 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123424, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123424, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22335 (p : Pattern) (ha : d123431 p = 1) (hb : d124830 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d15386 q = 1) (hb : d123425 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15386, d123425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15386, d123425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123430 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123431 q = 1) (hb : d124830 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123431, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123431, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22336 (p : Pattern) (ha : d123447 p = 1) (hb : d124835 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d15407 q = 1) (hb : d123446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15407, d123446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15407, d123446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123447 q = 1) (hb : d124835 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123447, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123447, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22337 (p : Pattern) (ha : d123462 p = 1) (hb : d124841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123432 q = 1) (hb : d124831 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123432, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22334 q ha hb
    | true =>
      simp only [d123432, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22335 q ha hb
  have h2 (q : Pattern) (ha : d123433 q = 1) (hb : d124832 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123433, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123433, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123434 q = 1) (hb : d124833 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123434, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123434, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123445 q = 1) (hb : d124834 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123445, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123445, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123448 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22335 q ha hb
    | true =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
  have h7 (q : Pattern) (ha : d123449 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123450 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123459 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123460 q = 1) (hb : d124839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123461 q = 1) (hb : d124840 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123461, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123461, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123462 q = 1) (hb : d124841 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123462, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123462, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22338 (p : Pattern) (ha : d6501 p = 1) (hb : d123456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6497 q = 1) (hb : d76226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6497, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5135 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6498 q = 1) (hb : d76227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6498, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6499 q = 1) (hb : d76228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6499, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6500 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6500, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6501 q = 1) (hb : d123456 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6501, d123456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6501, d123456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22339 (p : Pattern) (ha : d123467 p = 1) (hb : d124849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123448 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22335 q ha hb
    | true =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
  have h2 (q : Pattern) (ha : d123449 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123450 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123459 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123460 q = 1) (hb : d124839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123457 q = 1) (hb : d124844 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123457, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
    | true =>
      simp only [d123457, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22338 q hb ha
  have h7 (q : Pattern) (ha : d123458 q = 1) (hb : d124845 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123458, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123458, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123459 q = 1) (hb : d124846 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123459, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123459, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123465 q = 1) (hb : d124847 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123465, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123465, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123466 q = 1) (hb : d124848 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123466, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123466, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123467 q = 1) (hb : d124849 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123467, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123467, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22340 (p : Pattern) (ha : d123473 p = 1) (hb : d124855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123463 q = 1) (hb : d124842 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123463, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22337 q ha hb
    | true =>
      simp only [d123463, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123464 q = 1) (hb : d124843 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123464, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123464, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123468 q = 1) (hb : d124850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123468, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22339 q ha hb
    | true =>
      simp only [d123468, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123469 q = 1) (hb : d124851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123469, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123469, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123470 q = 1) (hb : d124852 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123470, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123470, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123471 q = 1) (hb : d124853 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123471, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123471, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123472 q = 1) (hb : d124854 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123472, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123472, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123473 q = 1) (hb : d124855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123473, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123473, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22341 (p : Pattern) (ha : d13516 p = 1) (hb : d123474 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13516 q = 1) (hb : d123474 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d123474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13516, d123474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22342 (p : Pattern) (ha : d123480 p = 1) (hb : d124861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123475 q = 1) (hb : d124856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123475, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
    | true =>
      simp only [d123475, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22341 q hb ha
  have h2 (q : Pattern) (ha : d123476 q = 1) (hb : d124857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123476, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123476, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123477 q = 1) (hb : d124858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123477, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123477, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123478 q = 1) (hb : d124859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123478, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123478, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123479 q = 1) (hb : d124860 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123479, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123479, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123480 q = 1) (hb : d124861 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123480, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123480, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22343 (p : Pattern) (ha : d123486 p = 1) (hb : d124867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123468 q = 1) (hb : d124850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123468, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22339 q ha hb
    | true =>
      simp only [d123468, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123469 q = 1) (hb : d124851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123469, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123469, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123481 q = 1) (hb : d124862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22342 q ha hb
    | true =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123482 q = 1) (hb : d124863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123483 q = 1) (hb : d124864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123483, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123483, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123484 q = 1) (hb : d124865 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123484, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123484, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123485 q = 1) (hb : d124866 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123485, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123485, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123486 q = 1) (hb : d124867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123486, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123486, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22344 (p : Pattern) (ha : d123507 p = 1) (hb : d124871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123448 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22335 q ha hb
    | true =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
  have h2 (q : Pattern) (ha : d123449 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123450 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123459 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123460 q = 1) (hb : d124839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123502 q = 1) (hb : d124856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123502, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
    | true =>
      simp only [d123502, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18688 q hb ha
  have h7 (q : Pattern) (ha : d123503 q = 1) (hb : d124857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123503, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123503, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123504 q = 1) (hb : d124858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123504, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123504, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123505 q = 1) (hb : d124859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123505, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123505, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123506 q = 1) (hb : d124870 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123506, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123506, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123507 q = 1) (hb : d124871 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123507, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123507, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22345 (p : Pattern) (ha : d123513 p = 1) (hb : d124877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123508 q = 1) (hb : d124872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123508, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22344 q ha hb
    | true =>
      simp only [d123508, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123509 q = 1) (hb : d124873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123509, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123509, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123510 q = 1) (hb : d124874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123510, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123510, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123511 q = 1) (hb : d124875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123511, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123511, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123512 q = 1) (hb : d124876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123512, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123512, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123513 q = 1) (hb : d124877 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123513, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123513, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22346 (p : Pattern) (ha : d123519 p = 1) (hb : d124883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123487 q = 1) (hb : d124868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123487, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22340 q ha hb
    | true =>
      simp only [d123487, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22343 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123501 q = 1) (hb : d124869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123501, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123501, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123514 q = 1) (hb : d124878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123514, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22345 q ha hb
    | true =>
      simp only [d123514, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123515 q = 1) (hb : d124879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123515, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123515, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123516 q = 1) (hb : d124880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123516, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123516, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123517 q = 1) (hb : d124881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123517, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123517, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123518 q = 1) (hb : d124882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123518, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123518, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123519 q = 1) (hb : d124883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123519, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123519, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22347 (p : Pattern) (ha : d123499 p = 1) (hb : d124888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123481 q = 1) (hb : d124862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22342 q ha hb
    | true =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123482 q = 1) (hb : d124863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123496 q = 1) (hb : d124885 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123496, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123496, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123497 q = 1) (hb : d124886 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123497, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123497, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123498 q = 1) (hb : d124887 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123498, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123498, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123499 q = 1) (hb : d124888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123499, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123499, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22348 (p : Pattern) (ha : d123526 p = 1) (hb : d124894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123521 q = 1) (hb : d124889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123521, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22347 q ha hb
    | true =>
      simp only [d123521, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123522 q = 1) (hb : d124890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123522, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123522, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123523 q = 1) (hb : d124891 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123523, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123523, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123524 q = 1) (hb : d124892 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123524, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123524, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123525 q = 1) (hb : d124893 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123525, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123525, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123526 q = 1) (hb : d124894 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123526, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123526, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22349 (p : Pattern) (ha : d123532 p = 1) (hb : d124900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123283 q = 1) (hb : d124708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123283, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123283, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22305 q ha hb
  have h2 (q : Pattern) (ha : d123284 q = 1) (hb : d124709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123284, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123284, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123293 q = 1) (hb : d124718 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123293, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22305 q ha hb
    | true =>
      simp only [d123293, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22308 q ha hb
  have h4 (q : Pattern) (ha : d123294 q = 1) (hb : d124719 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123294, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123294, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123295 q = 1) (hb : d124720 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123295, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123295, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123386 q = 1) (hb : d124797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123386, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22321 q ha hb
    | true =>
      simp only [d123386, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22329 q ha hb
  have h7 (q : Pattern) (ha : d123404 q = 1) (hb : d124815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123404, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22330 q ha hb
    | true =>
      simp only [d123404, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22331 q ha hb
  have h8 (q : Pattern) (ha : d123405 q = 1) (hb : d124816 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123405, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123405, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123406 q = 1) (hb : d124817 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123406, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123406, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123407 q = 1) (hb : d124818 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123407, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123407, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123411 q = 1) (hb : d124822 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123411, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123411, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22332 q ha hb
  have h12 (q : Pattern) (ha : d123413 q = 1) (hb : d124824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123413, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123413, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22333 q ha hb
  have h13 (q : Pattern) (ha : d123414 q = 1) (hb : d124825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123414, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123414, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123415 q = 1) (hb : d124826 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123415, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123415, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123416 q = 1) (hb : d124827 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123416, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d123416, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d123417 q = 1) (hb : d124828 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123417, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123417, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123520 q = 1) (hb : d124884 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123520, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123520, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22346 q ha hb
  have h18 (q : Pattern) (ha : d123527 q = 1) (hb : d124895 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123527, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123527, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22348 q ha hb
  have h19 (q : Pattern) (ha : d123528 q = 1) (hb : d124896 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123528, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123528, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123529 q = 1) (hb : d124897 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123529, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123529, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d123530 q = 1) (hb : d124898 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123530, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d123530, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d123531 q = 1) (hb : d124899 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123531, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123531, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123532 q = 1) (hb : d124900 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123532, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123532, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22350 (p : Pattern) (ha : d123538 p = 1) (hb : d124906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123533 q = 1) (hb : d124901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123533, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123533, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22349 q ha hb
  have h2 (q : Pattern) (ha : d123534 q = 1) (hb : d124902 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123534, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123534, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123535 q = 1) (hb : d124903 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123535, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123535, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123536 q = 1) (hb : d124904 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123536, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123536, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123537 q = 1) (hb : d124905 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123537, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123537, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123538 q = 1) (hb : d124906 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123538, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123538, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22351 (p : Pattern) (ha : d13614 p = 1) (hb : d123562 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13614 q = 1) (hb : d123562 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d123562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13614, d123562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22352 (p : Pattern) (ha : d123545 p = 1) (hb : d124911 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d15544 q = 1) (hb : d123543 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15544, d123543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15544, d123543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123544 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123545 q = 1) (hb : d124911 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123545, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d123545, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22353 (p : Pattern) (ha : d123550 p = 1) (hb : d124912 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d15547 q = 1) (hb : d123546 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15547, d123546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15547, d123546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123549 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123550 q = 1) (hb : d124912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123550, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d123550, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro22354 (p : Pattern) (ha : d123568 p = 1) (hb : d124922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123551 q = 1) (hb : d124913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22352 q ha hb
    | true =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
  have h2 (q : Pattern) (ha : d123552 q = 1) (hb : d124914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123553 q = 1) (hb : d124915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123560 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123561 q = 1) (hb : d124916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123563 q = 1) (hb : d124917 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123563, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
    | true =>
      simp only [d123563, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22351 q hb ha
  have h7 (q : Pattern) (ha : d123564 q = 1) (hb : d124918 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123564, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123564, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123565 q = 1) (hb : d124919 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123565, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123565, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123566 q = 1) (hb : d124920 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123566, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123566, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123567 q = 1) (hb : d124921 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123567, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123567, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123568 q = 1) (hb : d124922 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123568, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123568, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22355 (p : Pattern) (ha : d123572 p = 1) (hb : d124926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123563 q = 1) (hb : d124917 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123563, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
    | true =>
      simp only [d123563, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22351 q hb ha
  have h2 (q : Pattern) (ha : d123564 q = 1) (hb : d124918 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123564, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123564, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123565 q = 1) (hb : d124919 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123565, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123565, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123566 q = 1) (hb : d124920 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123566, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123566, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123571 q = 1) (hb : d124925 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123571, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123571, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123572 q = 1) (hb : d124926 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123572, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123572, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22356 (p : Pattern) (ha : d123578 p = 1) (hb : d124932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22354 q ha hb
    | true =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123577 q = 1) (hb : d124931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123577, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123577, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123578 q = 1) (hb : d124932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123578, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123578, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22357 (p : Pattern) (ha : d123582 p = 1) (hb : d124936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123581 q = 1) (hb : d124935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123581, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123581, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123582 q = 1) (hb : d124936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123582, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123582, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22358 (p : Pattern) (ha : d123588 p = 1) (hb : d124942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123583 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22356 q ha hb
    | true =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h2 (q : Pattern) (ha : d123584 q = 1) (hb : d124938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123584, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123584, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123585 q = 1) (hb : d124939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123585, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123585, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123586 q = 1) (hb : d124940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123586, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123586, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123587 q = 1) (hb : d124941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123587, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123587, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123588 q = 1) (hb : d124942 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123588, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123588, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22359 (p : Pattern) (ha : d123591 p = 1) (hb : d124945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22354 q ha hb
    | true =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123577 q = 1) (hb : d124931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123577, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123577, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123591 q = 1) (hb : d124945 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123591, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123591, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22360 (p : Pattern) (ha : d123592 p = 1) (hb : d124946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123581 q = 1) (hb : d124935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123581, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123581, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123592 q = 1) (hb : d124946 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123592, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123592, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22361 (p : Pattern) (ha : d123598 p = 1) (hb : d124952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123583 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22356 q ha hb
    | true =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h2 (q : Pattern) (ha : d123584 q = 1) (hb : d124938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123584, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123584, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123585 q = 1) (hb : d124939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123585, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123585, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123586 q = 1) (hb : d124940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123586, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123586, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123587 q = 1) (hb : d124941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123587, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123587, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123593 q = 1) (hb : d124947 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22359 q ha hb
    | true =>
      simp only [d123593, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22360 q ha hb
  have h7 (q : Pattern) (ha : d123594 q = 1) (hb : d124948 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123594, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123594, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123595 q = 1) (hb : d124949 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123595, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123595, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123596 q = 1) (hb : d124950 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123596, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123596, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123597 q = 1) (hb : d124951 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123597, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123597, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123598 q = 1) (hb : d124952 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123598, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123598, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22362 (p : Pattern) (ha : d123603 p = 1) (hb : d124957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22354 q ha hb
    | true =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123602 q = 1) (hb : d124956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123602, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123602, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123603 q = 1) (hb : d124957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123603, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123603, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22363 (p : Pattern) (ha : d123605 p = 1) (hb : d124959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123604 q = 1) (hb : d124958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123604, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123604, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123605 q = 1) (hb : d124959 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123605, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123605, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22364 (p : Pattern) (ha : d123612 p = 1) (hb : d124966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22354 q ha hb
    | true =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123610 q = 1) (hb : d124964 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123610, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123610, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123611 q = 1) (hb : d124965 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123611, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123611, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123612 q = 1) (hb : d124966 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123612, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123612, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22365 (p : Pattern) (ha : d123615 p = 1) (hb : d124969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123613 q = 1) (hb : d124967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123613, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123613, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123614 q = 1) (hb : d124968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123614, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123614, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123615 q = 1) (hb : d124969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123615, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123615, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22366 (p : Pattern) (ha : d15621 p = 1) (hb : d123620 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d15620 q = 1) (hb : d123619 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15620, d123619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15620, d123619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15621 q = 1) (hb : d123620 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15621, d123620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15621, d123620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22367 (p : Pattern) (ha : d123630 p = 1) (hb : d124978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123621 q = 1) (hb : d124973 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123621, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22366 q hb ha
    | true =>
      simp only [d123621, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22352 q ha hb
  have h2 (q : Pattern) (ha : d123622 q = 1) (hb : d124974 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123622, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123622, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123623 q = 1) (hb : d124975 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123623, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123623, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123627 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123628 q = 1) (hb : d124976 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123628, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123628, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123551 q = 1) (hb : d124913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22352 q ha hb
    | true =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
  have h7 (q : Pattern) (ha : d123552 q = 1) (hb : d124914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123553 q = 1) (hb : d124915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123560 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123561 q = 1) (hb : d124916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123629 q = 1) (hb : d124977 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123629, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123629, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123630 q = 1) (hb : d124978 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123630, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123630, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22368 (p : Pattern) (ha : d5252 p = 1) (hb : d123557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5248 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5249 q = 1) (hb : d69333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5249, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5250 q = 1) (hb : d69334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5250, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5251 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5251, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5252 q = 1) (hb : d123557 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5252, d123557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5252, d123557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22369 (p : Pattern) (ha : d123635 p = 1) (hb : d124986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123551 q = 1) (hb : d124913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22352 q ha hb
    | true =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
  have h2 (q : Pattern) (ha : d123552 q = 1) (hb : d124914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123553 q = 1) (hb : d124915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123560 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123561 q = 1) (hb : d124916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123558 q = 1) (hb : d124981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123558, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
    | true =>
      simp only [d123558, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22368 q hb ha
  have h7 (q : Pattern) (ha : d123559 q = 1) (hb : d124982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123559, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123559, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123560 q = 1) (hb : d124983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123560, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123560, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123633 q = 1) (hb : d124984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123633, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123633, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123634 q = 1) (hb : d124985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123634, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123634, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123635 q = 1) (hb : d124986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123635, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123635, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22370 (p : Pattern) (ha : d123641 p = 1) (hb : d124992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123631 q = 1) (hb : d124979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123631, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22367 q ha hb
    | true =>
      simp only [d123631, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123632 q = 1) (hb : d124980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123632, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123632, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123636 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22369 q ha hb
    | true =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123637 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123638 q = 1) (hb : d124989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123638, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123638, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123639 q = 1) (hb : d124990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123639, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123639, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123640 q = 1) (hb : d124991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123640, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123640, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123641 q = 1) (hb : d124992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123641, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123641, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22371 (p : Pattern) (ha : d123645 p = 1) (hb : d124996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123636 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22369 q ha hb
    | true =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123637 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123642 q = 1) (hb : d124993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123642, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123642, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123643 q = 1) (hb : d124994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123643, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123643, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123644 q = 1) (hb : d124995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123644, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123644, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123645 q = 1) (hb : d124996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123645, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123645, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22372 (p : Pattern) (ha : d123653 p = 1) (hb : d124922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123551 q = 1) (hb : d124913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22352 q ha hb
    | true =>
      simp only [d123551, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
  have h2 (q : Pattern) (ha : d123552 q = 1) (hb : d124914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123553 q = 1) (hb : d124915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123560 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123561 q = 1) (hb : d124916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123561, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123648 q = 1) (hb : d124917 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123648, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22353 q ha hb
    | true =>
      simp only [d123648, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18730 q hb ha
  have h7 (q : Pattern) (ha : d123649 q = 1) (hb : d124918 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123649, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123649, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123650 q = 1) (hb : d124919 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123650, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123650, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123651 q = 1) (hb : d124920 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123651, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123651, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123652 q = 1) (hb : d124921 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123652, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123652, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123653 q = 1) (hb : d124922 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123653, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123653, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22373 (p : Pattern) (ha : d123659 p = 1) (hb : d125002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123654 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123654, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22372 q ha hb
    | true =>
      simp only [d123654, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123655 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123655, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123655, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123656 q = 1) (hb : d124999 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123656, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123656, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123657 q = 1) (hb : d125000 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123657, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123657, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123658 q = 1) (hb : d125001 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123658, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123658, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123659 q = 1) (hb : d125002 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123659, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123659, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22374 (p : Pattern) (ha : d123665 p = 1) (hb : d125008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123606 q = 1) (hb : d124960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123606, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22362 q ha hb
    | true =>
      simp only [d123606, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22363 q ha hb
  have h2 (q : Pattern) (ha : d123607 q = 1) (hb : d124961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123607, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123607, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123608 q = 1) (hb : d124962 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123608, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123608, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123609 q = 1) (hb : d124963 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123609, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123609, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123616 q = 1) (hb : d124970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123616, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22364 q ha hb
    | true =>
      simp only [d123616, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22365 q ha hb
  have h6 (q : Pattern) (ha : d123617 q = 1) (hb : d124971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123617, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123617, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123618 q = 1) (hb : d124972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123618, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123618, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123646 q = 1) (hb : d124997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123646, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22370 q ha hb
    | true =>
      simp only [d123646, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22371 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123583 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123647 q = 1) (hb : d124998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123647, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123660 q = 1) (hb : d125003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123660, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22373 q ha hb
    | true =>
      simp only [d123660, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123661 q = 1) (hb : d125004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123661, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123661, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123662 q = 1) (hb : d125005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123662, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123663 q = 1) (hb : d125006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123663, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123664 q = 1) (hb : d125007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123664, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123665 q = 1) (hb : d125008 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123665, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123665, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro22375 (p : Pattern) (ha : d123666 p = 1) (hb : d125009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22354 q ha hb
    | true =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123602 q = 1) (hb : d124956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123602, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123602, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123666 q = 1) (hb : d125009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123666, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123666, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22376 (p : Pattern) (ha : d123667 p = 1) (hb : d125010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123604 q = 1) (hb : d124958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123604, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123604, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123667 q = 1) (hb : d125010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123667, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123667, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22377 (p : Pattern) (ha : d123672 p = 1) (hb : d125015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22354 q ha hb
    | true =>
      simp only [d123569, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123610 q = 1) (hb : d124964 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123610, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123610, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123611 q = 1) (hb : d124965 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123611, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123611, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123672 q = 1) (hb : d125015 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123672, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123672, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22378 (p : Pattern) (ha : d123673 p = 1) (hb : d125016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123613 q = 1) (hb : d124967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123613, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123613, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123614 q = 1) (hb : d124968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123614, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123614, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123673 q = 1) (hb : d125016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123673, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123673, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22379 (p : Pattern) (ha : d123677 p = 1) (hb : d125020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123631 q = 1) (hb : d124979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123631, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22367 q ha hb
    | true =>
      simp only [d123631, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123632 q = 1) (hb : d124980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123632, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123632, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123636 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22369 q ha hb
    | true =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123637 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123638 q = 1) (hb : d124989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123638, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123638, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123639 q = 1) (hb : d124990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123639, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123639, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123640 q = 1) (hb : d124991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123640, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123640, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123677 q = 1) (hb : d125020 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123677, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123677, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22380 (p : Pattern) (ha : d123678 p = 1) (hb : d125021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123636 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22369 q ha hb
    | true =>
      simp only [d123636, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123637 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22355 q ha hb
    | true =>
      simp only [d123573, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123642 q = 1) (hb : d124993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123642, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123642, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123643 q = 1) (hb : d124994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123643, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123643, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123644 q = 1) (hb : d124995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123644, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123644, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123678 q = 1) (hb : d125021 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123678, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123678, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22381 (p : Pattern) (ha : d123681 p = 1) (hb : d125024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123654 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123654, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22372 q ha hb
    | true =>
      simp only [d123654, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123655 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123655, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123655, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123656 q = 1) (hb : d124999 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123656, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123656, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123657 q = 1) (hb : d125000 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123657, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123657, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123658 q = 1) (hb : d125001 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123658, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123658, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123681 q = 1) (hb : d125024 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123681, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123681, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22382 (p : Pattern) (ha : d123687 p = 1) (hb : d125030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123606 q = 1) (hb : d124960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123606, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22362 q ha hb
    | true =>
      simp only [d123606, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22363 q ha hb
  have h2 (q : Pattern) (ha : d123607 q = 1) (hb : d124961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123607, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123607, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123608 q = 1) (hb : d124962 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123608, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123608, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123609 q = 1) (hb : d124963 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123609, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123609, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123616 q = 1) (hb : d124970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123616, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22364 q ha hb
    | true =>
      simp only [d123616, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22365 q ha hb
  have h6 (q : Pattern) (ha : d123617 q = 1) (hb : d124971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123617, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123617, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123618 q = 1) (hb : d124972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123618, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123618, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123646 q = 1) (hb : d124997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123646, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22370 q ha hb
    | true =>
      simp only [d123646, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22371 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123583 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123647 q = 1) (hb : d124998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123647, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123660 q = 1) (hb : d125003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123660, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22373 q ha hb
    | true =>
      simp only [d123660, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123661 q = 1) (hb : d125004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123661, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123661, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123662 q = 1) (hb : d125005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123662, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123663 q = 1) (hb : d125006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123663, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123664 q = 1) (hb : d125007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123664, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123668 q = 1) (hb : d125011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123668, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22375 q ha hb
    | true =>
      simp only [d123668, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22376 q ha hb
  have h17 (q : Pattern) (ha : d123669 q = 1) (hb : d125012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123669, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123669, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123670 q = 1) (hb : d125013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123670, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123670, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d123671 q = 1) (hb : d125014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123671, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123671, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123674 q = 1) (hb : d125017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123674, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22377 q ha hb
    | true =>
      simp only [d123674, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22378 q ha hb
  have h21 (q : Pattern) (ha : d123675 q = 1) (hb : d125018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123675, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123675, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d123676 q = 1) (hb : d125019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123676, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123676, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123679 q = 1) (hb : d125022 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123679, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22379 q ha hb
    | true =>
      simp only [d123679, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22380 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d123680 q = 1) (hb : d125023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d123680, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d123682 q = 1) (hb : d125025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123682, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22381 q ha hb
    | true =>
      simp only [d123682, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d123683 q = 1) (hb : d125026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123683, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d123683, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d123684 q = 1) (hb : d125027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d123684, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d123685 q = 1) (hb : d125028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123685, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d123685, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d123686 q = 1) (hb : d125029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123686, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123686, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d123687 q = 1) (hb : d125030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123687, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123687, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro22383 (p : Pattern) (ha : d123699 p = 1) (hb : d125042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123689 q = 1) (hb : d125032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123689, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22371 q ha hb
    | true =>
      simp only [d123689, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h2 (q : Pattern) (ha : d123690 q = 1) (hb : d125033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123690, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123690, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123691 q = 1) (hb : d125034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123691, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123691, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123692 q = 1) (hb : d125035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123692, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123692, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123693 q = 1) (hb : d125036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123693, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123693, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123694 q = 1) (hb : d125037 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123694, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
    | true =>
      simp only [d123694, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123695 q = 1) (hb : d125038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123695, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123695, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123696 q = 1) (hb : d125039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123696, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123696, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123697 q = 1) (hb : d125040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123697, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123697, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123698 q = 1) (hb : d125041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123698, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123698, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123699 q = 1) (hb : d125042 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123699, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123699, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22384 (p : Pattern) (ha : d123705 p = 1) (hb : d125048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123694 q = 1) (hb : d125037 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123694, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
    | true =>
      simp only [d123694, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123695 q = 1) (hb : d125038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123695, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123695, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123696 q = 1) (hb : d125039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123696, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123696, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123697 q = 1) (hb : d125040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123697, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123697, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123698 q = 1) (hb : d125041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123698, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123698, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123700 q = 1) (hb : d125043 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123700, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22360 q ha hb
    | true =>
      simp only [d123700, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123701 q = 1) (hb : d125044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123701, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123701, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123702 q = 1) (hb : d125045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123702, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123702, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123703 q = 1) (hb : d125046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123703, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123703, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123704 q = 1) (hb : d125047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123704, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123704, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123705 q = 1) (hb : d125048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123705, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123705, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro22385 (p : Pattern) (ha : d123712 p = 1) (hb : d125055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123679 q = 1) (hb : d125022 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123679, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22379 q ha hb
    | true =>
      simp only [d123679, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22380 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123680 q = 1) (hb : d125023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123680, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123682 q = 1) (hb : d125025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123682, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22381 q ha hb
    | true =>
      simp only [d123682, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123683 q = 1) (hb : d125026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123683, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123683, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123684 q = 1) (hb : d125027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123684, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123710 q = 1) (hb : d125053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123710, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123710, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123711 q = 1) (hb : d125054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123711, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123711, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123712 q = 1) (hb : d125055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123712, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123712, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22386 (p : Pattern) (ha : d123714 p = 1) (hb : d125057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123700 q = 1) (hb : d125043 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123700, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22360 q ha hb
    | true =>
      simp only [d123700, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123701 q = 1) (hb : d125044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123701, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123701, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123702 q = 1) (hb : d125045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123702, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123702, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123703 q = 1) (hb : d125046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123703, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123703, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123704 q = 1) (hb : d125047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123704, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123704, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123714 q = 1) (hb : d125057 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123714, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123714, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22387 (p : Pattern) (ha : d15768 p = 1) (hb : d123721 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d15767 q = 1) (hb : d123720 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15767, d123720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15767, d123720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15768 q = 1) (hb : d123721 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15768, d123721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15768, d123721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22388 (p : Pattern) (ha : d123724 p = 1) (hb : d125063 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d15769 q = 1) (hb : d123722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15769, d123722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15769, d123722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123723 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123724 q = 1) (hb : d125063 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123724, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123724, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22389 (p : Pattern) (ha : d123739 p = 1) (hb : d125068 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d15785 q = 1) (hb : d123738 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15785, d123738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15785, d123738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123739 q = 1) (hb : d125068 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123739, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123739, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro22390 (p : Pattern) (ha : d123754 p = 1) (hb : d125074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123725 q = 1) (hb : d125064 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123725, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22387 q hb ha
    | true =>
      simp only [d123725, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
  have h2 (q : Pattern) (ha : d123726 q = 1) (hb : d125065 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123726, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123726, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123727 q = 1) (hb : d125066 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123727, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123727, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123736 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123737 q = 1) (hb : d125067 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123737, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123737, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h7 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123751 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123752 q = 1) (hb : d125072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123753 q = 1) (hb : d125073 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123753, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123753, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123754 q = 1) (hb : d125074 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123754, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123754, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro22391 (p : Pattern) (ha : d6648 p = 1) (hb : d123748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6644 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5248 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6645 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6645, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6646 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6646, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6647 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6647, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6648 q = 1) (hb : d123748 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6648, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6648, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22392 (p : Pattern) (ha : d123759 p = 1) (hb : d125082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123752 q = 1) (hb : d125072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123749 q = 1) (hb : d125077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123749, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22391 q hb ha
  have h7 (q : Pattern) (ha : d123750 q = 1) (hb : d125078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123751 q = 1) (hb : d125079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123757 q = 1) (hb : d125080 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123757, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123757, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123758 q = 1) (hb : d125081 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123758, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123758, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123759 q = 1) (hb : d125082 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123759, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123759, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22393 (p : Pattern) (ha : d123765 p = 1) (hb : d125088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123755 q = 1) (hb : d125075 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123755, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22390 q ha hb
    | true =>
      simp only [d123755, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123756 q = 1) (hb : d125076 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123756, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123756, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123760 q = 1) (hb : d125083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123760, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22392 q ha hb
    | true =>
      simp only [d123760, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123761 q = 1) (hb : d125084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123761, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123761, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123762 q = 1) (hb : d125085 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123762, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123762, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123763 q = 1) (hb : d125086 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123763, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123763, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123764 q = 1) (hb : d125087 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123764, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123764, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123765 q = 1) (hb : d125088 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123765, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123765, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22394 (p : Pattern) (ha : d13843 p = 1) (hb : d123766 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13843 q = 1) (hb : d123766 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d123766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13843, d123766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22395 (p : Pattern) (ha : d123772 p = 1) (hb : d125094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123767 q = 1) (hb : d125089 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123767, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123767, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22394 q hb ha
  have h2 (q : Pattern) (ha : d123768 q = 1) (hb : d125090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123768, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123768, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123769 q = 1) (hb : d125091 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123769, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123769, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123770 q = 1) (hb : d125092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123770, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123770, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123771 q = 1) (hb : d125093 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123771, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123771, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123772 q = 1) (hb : d125094 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123772, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123772, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22396 (p : Pattern) (ha : d123778 p = 1) (hb : d125100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123760 q = 1) (hb : d125083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123760, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22392 q ha hb
    | true =>
      simp only [d123760, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123761 q = 1) (hb : d125084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123761, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123761, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123773 q = 1) (hb : d125095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22395 q ha hb
    | true =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123774 q = 1) (hb : d125096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123775 q = 1) (hb : d125097 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123775, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123775, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123776 q = 1) (hb : d125098 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123776, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123776, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123777 q = 1) (hb : d125099 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123777, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123777, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123778 q = 1) (hb : d125100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123778, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123778, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22397 (p : Pattern) (ha : d123799 p = 1) (hb : d125104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123752 q = 1) (hb : d125072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123794 q = 1) (hb : d125089 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123794, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123794, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18736 q hb ha
  have h7 (q : Pattern) (ha : d123795 q = 1) (hb : d125090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123795, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123795, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123796 q = 1) (hb : d125091 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123796, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123796, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123797 q = 1) (hb : d125092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123797, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123797, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123798 q = 1) (hb : d125103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123798, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123798, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123799 q = 1) (hb : d125104 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123799, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123799, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22398 (p : Pattern) (ha : d123805 p = 1) (hb : d125110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123800 q = 1) (hb : d125105 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123800, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22397 q ha hb
    | true =>
      simp only [d123800, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123801 q = 1) (hb : d125106 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123801, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123801, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123802 q = 1) (hb : d125107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123802, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123802, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123803 q = 1) (hb : d125108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123803, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123803, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123804 q = 1) (hb : d125109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123804, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123804, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123805 q = 1) (hb : d125110 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123805, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123805, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22399 (p : Pattern) (ha : d123811 p = 1) (hb : d125116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123779 q = 1) (hb : d125101 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123779, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22393 q ha hb
    | true =>
      simp only [d123779, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123792 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123793 q = 1) (hb : d125102 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123793, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123793, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123806 q = 1) (hb : d125111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123806, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22398 q ha hb
    | true =>
      simp only [d123806, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123807 q = 1) (hb : d125112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123807, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123807, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123808 q = 1) (hb : d125113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123808, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123808, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123809 q = 1) (hb : d125114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123809, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123809, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123810 q = 1) (hb : d125115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123810, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123810, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123811 q = 1) (hb : d125116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123811, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123811, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro22400 (p : Pattern) (ha : d123791 p = 1) (hb : d125121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123773 q = 1) (hb : d125095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22395 q ha hb
    | true =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123774 q = 1) (hb : d125096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123788 q = 1) (hb : d125118 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123788, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123788, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123789 q = 1) (hb : d125119 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123789, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123789, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123790 q = 1) (hb : d125120 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123790, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123790, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123791 q = 1) (hb : d125121 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123791, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123791, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22401 (p : Pattern) (ha : d123818 p = 1) (hb : d125127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123813 q = 1) (hb : d125122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123813, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22400 q ha hb
    | true =>
      simp only [d123813, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123814 q = 1) (hb : d125123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123814, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123814, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123815 q = 1) (hb : d125124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123815, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123815, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123816 q = 1) (hb : d125125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123816, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123816, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123817 q = 1) (hb : d125126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123817, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123817, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123818 q = 1) (hb : d125127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123818, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123818, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22402 (p : Pattern) (ha : d123824 p = 1) (hb : d125133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123589 q = 1) (hb : d124943 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123589, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123589, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22358 q ha hb
  have h2 (q : Pattern) (ha : d123590 q = 1) (hb : d124944 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123590, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123590, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123599 q = 1) (hb : d124953 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123599, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22358 q ha hb
    | true =>
      simp only [d123599, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22361 q ha hb
  have h4 (q : Pattern) (ha : d123600 q = 1) (hb : d124954 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123600, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123600, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123601 q = 1) (hb : d124955 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123601, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123601, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123688 q = 1) (hb : d125031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123688, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22374 q ha hb
    | true =>
      simp only [d123688, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22382 q ha hb
  have h7 (q : Pattern) (ha : d123706 q = 1) (hb : d125049 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123706, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22383 q ha hb
    | true =>
      simp only [d123706, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22384 q ha hb
  have h8 (q : Pattern) (ha : d123707 q = 1) (hb : d125050 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123707, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123707, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123708 q = 1) (hb : d125051 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123708, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123708, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123709 q = 1) (hb : d125052 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123709, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123709, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123713 q = 1) (hb : d125056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123713, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123713, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22385 q ha hb
  have h12 (q : Pattern) (ha : d123715 q = 1) (hb : d125058 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123715, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123715, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22386 q ha hb
  have h13 (q : Pattern) (ha : d123716 q = 1) (hb : d125059 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123716, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123716, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123717 q = 1) (hb : d125060 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123717, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123717, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123718 q = 1) (hb : d125061 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123718, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d123718, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d123719 q = 1) (hb : d125062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123719, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123719, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123812 q = 1) (hb : d125117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123812, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123812, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22399 q ha hb
  have h18 (q : Pattern) (ha : d123819 q = 1) (hb : d125128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123819, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123819, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22401 q ha hb
  have h19 (q : Pattern) (ha : d123820 q = 1) (hb : d125129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123820, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123820, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123821 q = 1) (hb : d125130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123821, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123821, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d123822 q = 1) (hb : d125131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123822, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d123822, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d123823 q = 1) (hb : d125132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123823, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123823, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123824 q = 1) (hb : d125133 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123824, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123824, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro22403 (p : Pattern) (ha : d123830 p = 1) (hb : d125139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123825 q = 1) (hb : d125134 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123825, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123825, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22402 q ha hb
  have h2 (q : Pattern) (ha : d123826 q = 1) (hb : d125135 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123826, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123826, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123827 q = 1) (hb : d125136 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123827, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123827, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123828 q = 1) (hb : d125137 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123828, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123828, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123829 q = 1) (hb : d125138 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123829, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123829, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123830 q = 1) (hb : d125139 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123830, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123830, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22404 (p : Pattern) (ha : d123836 p = 1) (hb : d125145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d122703 q = 1) (hb : d124246 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122703, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22162 q ha hb
    | true =>
      simp only [d122703, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22202 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122926 q = 1) (hb : d124440 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122926, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122926, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22244 q ha hb
  have h3 (q : Pattern) (ha : d122927 q = 1) (hb : d124441 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d122927, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d122927, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123232 q = 1) (hb : d124673 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123232, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123232, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22297 q ha hb
  have h5 (q : Pattern) (ha : d123233 q = 1) (hb : d124674 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123233, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123233, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123234 q = 1) (hb : d124675 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123234, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123234, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123539 q = 1) (hb : d124907 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123539, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123539, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22350 q ha hb
  have h8 (q : Pattern) (ha : d123540 q = 1) (hb : d124908 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123540, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123540, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123541 q = 1) (hb : d124909 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123541, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123541, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123542 q = 1) (hb : d124910 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123542, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123542, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123831 q = 1) (hb : d125140 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123831, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123831, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22403 q ha hb
  have h12 (q : Pattern) (ha : d123832 q = 1) (hb : d125141 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123832, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123832, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123833 q = 1) (hb : d125142 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123833, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123833, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123834 q = 1) (hb : d125143 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123834, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123834, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123835 q = 1) (hb : d125144 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d123835, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123835, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123836 q = 1) (hb : d125145 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d123836, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123836, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro22405 (p : Pattern) (ha : d123842 p = 1) (hb : d125151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d125146 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22404 q ha hb
    | true =>
      simp only [d123837, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d125147 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d125148 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d125149 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d125150 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d125151 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22406 (p : Pattern) (ha : d123848 p = 1) (hb : d125157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d125152 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22405 q ha hb
    | true =>
      simp only [d123843, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d125153 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d125154 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d125155 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d125156 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d125157 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22407 (p : Pattern) (ha : d123854 p = 1) (hb : d125163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d125158 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22406 q ha hb
    | true =>
      simp only [d123849, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d125159 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d125160 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d125161 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d125162 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d125163 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22408 (p : Pattern) (ha : d123860 p = 1) (hb : d125169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d125164 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22407 q ha hb
    | true =>
      simp only [d123855, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d125165 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d125166 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d125167 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d125168 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d125169 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22409 (p : Pattern) (ha : d123866 p = 1) (hb : d125175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d125170 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22408 q ha hb
    | true =>
      simp only [d123861, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d125171 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d125172 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d125173 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d125174 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d125175 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22410 (p : Pattern) (ha : d123872 p = 1) (hb : d125181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d125176 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22409 q ha hb
    | true =>
      simp only [d123867, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d125177 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d125178 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d125179 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d125180 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d125181 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22411 (p : Pattern) (ha : d123878 p = 1) (hb : d125187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d125182 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22410 q ha hb
    | true =>
      simp only [d123873, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d125183 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d125184 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d125185 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d125186 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d125187 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22412 (p : Pattern) (ha : d94521 p = 1) (hb : d122306 p = 1) : d125190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21839 q ha hb
    | true =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8292 q = 1) (hb : d122306 q = 1) : d123954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8293 q = 1) (hb : d122306 q = 1) : d123955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8293, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8294 q = 1) (hb : d122306 q = 1) : d123956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8295 q = 1) (hb : d122306 q = 1) : d123957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94521 q = 1) (hb : d122306 q = 1) : d125190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94521, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94521, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22413 (p : Pattern) (ha : d94531 p = 1) (hb : d122306 p = 1) : d125200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122306 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d122306 q = 1) : d123930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21844 q ha hb
    | true =>
      simp only [d8268, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94527 q = 1) (hb : d122306 q = 1) : d125196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94527, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94527, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94528 q = 1) (hb : d122306 q = 1) : d125197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94528, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94528, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94529 q = 1) (hb : d122306 q = 1) : d125198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94529, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94529, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94530 q = 1) (hb : d122306 q = 1) : d125199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94530, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94530, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94531 q = 1) (hb : d122306 q = 1) : d125200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94531, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94531, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22414 (p : Pattern) (ha : d94537 p = 1) (hb : d122306 p = 1) : d125206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8297 q = 1) (hb : d122306 q = 1) : d123959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21847 q ha hb
    | true =>
      simp only [d8297, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21848 q ha hb
  have h2 (q : Pattern) (ha : d8298 q = 1) (hb : d122306 q = 1) : d123960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8298, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94519 q = 1) (hb : d122306 q = 1) : d125188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94519, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94519, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94520 q = 1) (hb : d122306 q = 1) : d125189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94520, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94520, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94522 q = 1) (hb : d122306 q = 1) : d125191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94522, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94522, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22412 q ha hb
  have h6 (q : Pattern) (ha : d94523 q = 1) (hb : d122306 q = 1) : d125192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94523, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94523, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94524 q = 1) (hb : d122306 q = 1) : d125193 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94524, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94524, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94525 q = 1) (hb : d122306 q = 1) : d125194 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94525, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94525, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94526 q = 1) (hb : d122306 q = 1) : d125195 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94526, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94526, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94532 q = 1) (hb : d122306 q = 1) : d125201 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94532, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94532, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22413 q ha hb
  have h11 (q : Pattern) (ha : d94533 q = 1) (hb : d122306 q = 1) : d125202 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94533, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94533, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94534 q = 1) (hb : d122306 q = 1) : d125203 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94534, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94534, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94535 q = 1) (hb : d122306 q = 1) : d125204 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94535, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94535, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94536 q = 1) (hb : d122306 q = 1) : d125205 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94536, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94536, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94537 q = 1) (hb : d122306 q = 1) : d125206 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94537, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94537, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22415 (p : Pattern) (ha : d94543 p = 1) (hb : d122306 p = 1) : d125212 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d122306 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94538 q = 1) (hb : d122306 q = 1) : d125207 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94538, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94538, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22414 q ha hb
  have h3 (q : Pattern) (ha : d94539 q = 1) (hb : d122306 q = 1) : d125208 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94539, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94539, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94540 q = 1) (hb : d122306 q = 1) : d125209 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94540, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94540, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94541 q = 1) (hb : d122306 q = 1) : d125210 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94541, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94541, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94542 q = 1) (hb : d122306 q = 1) : d125211 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94542, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94542, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94543 q = 1) (hb : d122306 q = 1) : d125212 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94543, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94543, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro22416 (p : Pattern) (ha : d94546 p = 1) (hb : d122306 p = 1) : d125215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8430 q = 1) (hb : d122306 q = 1) : d124091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21880 q ha hb
    | true =>
      simp only [d8430, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21872 q ha hb
  have h2 (q : Pattern) (ha : d8431 q = 1) (hb : d122306 q = 1) : d124092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8432 q = 1) (hb : d122306 q = 1) : d124093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8432, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8433 q = 1) (hb : d122306 q = 1) : d124094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8434 q = 1) (hb : d122306 q = 1) : d124095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94546 q = 1) (hb : d122306 q = 1) : d125215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94546, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94546, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22417 (p : Pattern) (ha : d94555 p = 1) (hb : d122306 p = 1) : d124210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21864 q ha hb
    | true =>
      simp only [d8378, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d122306 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21875 q ha hb
    | true =>
      simp only [d684, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d122306 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94552 q = 1) (hb : d122306 q = 1) : d124207 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94552, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94552, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94553 q = 1) (hb : d122306 q = 1) : d124208 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94553, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94553, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94554 q = 1) (hb : d122306 q = 1) : d124209 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94554, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94554, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94555 q = 1) (hb : d122306 q = 1) : d124210 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94555, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94555, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22418 (p : Pattern) (ha : d94561 p = 1) (hb : d122306 p = 1) : d125226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94556 q = 1) (hb : d122306 q = 1) : d125221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94556, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22417 q ha hb
    | true =>
      simp only [d94556, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21876 q ha hb
  have h2 (q : Pattern) (ha : d94557 q = 1) (hb : d122306 q = 1) : d125222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94557, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94557, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94558 q = 1) (hb : d122306 q = 1) : d125223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94558, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94558, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94559 q = 1) (hb : d122306 q = 1) : d125224 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94559, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94559, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94560 q = 1) (hb : d122306 q = 1) : d125225 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94560, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94560, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94561 q = 1) (hb : d122306 q = 1) : d125226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94561, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94561, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22419 (p : Pattern) (ha : d94567 p = 1) (hb : d122306 p = 1) : d125232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d122306 q = 1) : d124097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21879 q ha hb
    | true =>
      simp only [d8436, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21881 q ha hb
  have h2 (q : Pattern) (ha : d8437 q = 1) (hb : d122306 q = 1) : d124098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94544 q = 1) (hb : d122306 q = 1) : d125213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94544, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94544, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94545 q = 1) (hb : d122306 q = 1) : d125214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94545, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94545, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94547 q = 1) (hb : d122306 q = 1) : d125216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94547, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94547, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22416 q ha hb
  have h6 (q : Pattern) (ha : d94548 q = 1) (hb : d122306 q = 1) : d125217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94548, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94548, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94549 q = 1) (hb : d122306 q = 1) : d125218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94549, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94549, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94550 q = 1) (hb : d122306 q = 1) : d125219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94550, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94550, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94551 q = 1) (hb : d122306 q = 1) : d125220 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94551, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94551, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94562 q = 1) (hb : d122306 q = 1) : d125227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94562, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94562, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22418 q ha hb
  have h11 (q : Pattern) (ha : d94563 q = 1) (hb : d122306 q = 1) : d125228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94563, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94563, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94564 q = 1) (hb : d122306 q = 1) : d125229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94564, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94564, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94565 q = 1) (hb : d122306 q = 1) : d125230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94565, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94565, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94566 q = 1) (hb : d122306 q = 1) : d125231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94566, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94566, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94567 q = 1) (hb : d122306 q = 1) : d125232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94567, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94567, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22420 (p : Pattern) (ha : d94573 p = 1) (hb : d122306 p = 1) : d125238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94568 q = 1) (hb : d122306 q = 1) : d125233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94568, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94568, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22419 q ha hb
  have h2 (q : Pattern) (ha : d94569 q = 1) (hb : d122306 q = 1) : d125234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94569, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94569, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94570 q = 1) (hb : d122306 q = 1) : d125235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94570, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94570, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94571 q = 1) (hb : d122306 q = 1) : d125236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94571, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94571, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94572 q = 1) (hb : d122306 q = 1) : d125237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94572, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94572, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94573 q = 1) (hb : d122306 q = 1) : d125238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94573, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94573, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22421 (p : Pattern) (ha : d94577 p = 1) (hb : d122306 p = 1) : d125242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8592 q = 1) (hb : d122306 q = 1) : d124277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21928 q ha hb
    | true =>
      simp only [d8592, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21917 q ha hb
  have h2 (q : Pattern) (ha : d8593 q = 1) (hb : d122306 q = 1) : d124278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8594 q = 1) (hb : d122306 q = 1) : d124279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8594, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8595 q = 1) (hb : d122306 q = 1) : d124280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8596 q = 1) (hb : d122306 q = 1) : d124281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94577 q = 1) (hb : d122306 q = 1) : d125242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94577, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94577, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22422 (p : Pattern) (ha : d94586 p = 1) (hb : d122306 p = 1) : d124404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d122306 q = 1) : d124391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21959 q ha hb
    | true =>
      simp only [d8716, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d122306 q = 1) : d124392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d122306 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21921 q ha hb
    | true =>
      simp only [d1006, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d122306 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94583 q = 1) (hb : d122306 q = 1) : d124401 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94583, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94583, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94584 q = 1) (hb : d122306 q = 1) : d124402 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94584, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94584, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94585 q = 1) (hb : d122306 q = 1) : d124403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94585, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94585, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94586 q = 1) (hb : d122306 q = 1) : d124404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94586, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94586, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22423 (p : Pattern) (ha : d94592 p = 1) (hb : d122306 p = 1) : d125253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94587 q = 1) (hb : d122306 q = 1) : d125248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94587, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22422 q ha hb
    | true =>
      simp only [d94587, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21922 q ha hb
  have h2 (q : Pattern) (ha : d94588 q = 1) (hb : d122306 q = 1) : d125249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94588, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94588, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94589 q = 1) (hb : d122306 q = 1) : d125250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94589, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94589, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94590 q = 1) (hb : d122306 q = 1) : d125251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94590, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94590, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94591 q = 1) (hb : d122306 q = 1) : d125252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94591, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94591, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94592 q = 1) (hb : d122306 q = 1) : d125253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94592, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94592, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22424 (p : Pattern) (ha : d94598 p = 1) (hb : d122306 p = 1) : d125259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d122306 q = 1) : d124283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21927 q ha hb
    | true =>
      simp only [d8598, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21929 q ha hb
  have h2 (q : Pattern) (ha : d8599 q = 1) (hb : d122306 q = 1) : d124284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94575 q = 1) (hb : d122306 q = 1) : d125240 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94575, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94575, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94576 q = 1) (hb : d122306 q = 1) : d125241 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94576, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94576, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94578 q = 1) (hb : d122306 q = 1) : d125243 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94578, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94578, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22421 q ha hb
  have h6 (q : Pattern) (ha : d94579 q = 1) (hb : d122306 q = 1) : d125244 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94579, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94579, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94580 q = 1) (hb : d122306 q = 1) : d125245 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94580, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94580, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94581 q = 1) (hb : d122306 q = 1) : d125246 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94581, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94581, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94582 q = 1) (hb : d122306 q = 1) : d125247 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94582, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94582, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94593 q = 1) (hb : d122306 q = 1) : d125254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94593, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94593, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22423 q ha hb
  have h11 (q : Pattern) (ha : d94594 q = 1) (hb : d122306 q = 1) : d125255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94594, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94594, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94595 q = 1) (hb : d122306 q = 1) : d125256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94595, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94595, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94596 q = 1) (hb : d122306 q = 1) : d125257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94596, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94596, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94597 q = 1) (hb : d122306 q = 1) : d125258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94597, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94597, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94598 q = 1) (hb : d122306 q = 1) : d125259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94598, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94598, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22425 (p : Pattern) (ha : d94604 p = 1) (hb : d122306 p = 1) : d125265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94599 q = 1) (hb : d122306 q = 1) : d125260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94599, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94599, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22424 q ha hb
  have h2 (q : Pattern) (ha : d94600 q = 1) (hb : d122306 q = 1) : d125261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94600, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94600, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94601 q = 1) (hb : d122306 q = 1) : d125262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94601, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94601, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94602 q = 1) (hb : d122306 q = 1) : d125263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94602, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94602, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94603 q = 1) (hb : d122306 q = 1) : d125264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94603, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94603, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94604 q = 1) (hb : d122306 q = 1) : d125265 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94604, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94604, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22426 (p : Pattern) (ha : d94609 p = 1) (hb : d122306 p = 1) : d125270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8759 q = 1) (hb : d122306 q = 1) : d124478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21980 q ha hb
    | true =>
      simp only [d8759, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21968 q ha hb
  have h2 (q : Pattern) (ha : d8760 q = 1) (hb : d122306 q = 1) : d124479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8761 q = 1) (hb : d122306 q = 1) : d124480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8761, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8762 q = 1) (hb : d122306 q = 1) : d124481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8763 q = 1) (hb : d122306 q = 1) : d124482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94609 q = 1) (hb : d122306 q = 1) : d125270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94609, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94609, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22427 (p : Pattern) (ha : d94618 p = 1) (hb : d122306 p = 1) : d125279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d122306 q = 1) : d124638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22011 q ha hb
    | true =>
      simp only [d8883, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d122306 q = 1) : d124639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d122306 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21973 q ha hb
    | true =>
      simp only [d1431, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d122306 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94615 q = 1) (hb : d122306 q = 1) : d125276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94615, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94615, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94616 q = 1) (hb : d122306 q = 1) : d125277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94616, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94616, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94617 q = 1) (hb : d122306 q = 1) : d125278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94617, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94617, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94618 q = 1) (hb : d122306 q = 1) : d125279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94618, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94618, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22428 (p : Pattern) (ha : d94624 p = 1) (hb : d122306 p = 1) : d125285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94619 q = 1) (hb : d122306 q = 1) : d125280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94619, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22427 q ha hb
    | true =>
      simp only [d94619, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21974 q ha hb
  have h2 (q : Pattern) (ha : d94620 q = 1) (hb : d122306 q = 1) : d125281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94620, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94620, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94621 q = 1) (hb : d122306 q = 1) : d125282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94621, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94621, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94622 q = 1) (hb : d122306 q = 1) : d125283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94622, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94622, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94623 q = 1) (hb : d122306 q = 1) : d125284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94623, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94623, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94624 q = 1) (hb : d122306 q = 1) : d125285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94624, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94624, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22429 (p : Pattern) (ha : d94630 p = 1) (hb : d122306 p = 1) : d125291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d122306 q = 1) : d124484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21979 q ha hb
    | true =>
      simp only [d8765, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21981 q ha hb
  have h2 (q : Pattern) (ha : d8766 q = 1) (hb : d122306 q = 1) : d124485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94607 q = 1) (hb : d122306 q = 1) : d125268 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94607, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94607, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94608 q = 1) (hb : d122306 q = 1) : d125269 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94608, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94608, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94610 q = 1) (hb : d122306 q = 1) : d125271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94610, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94610, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22426 q ha hb
  have h6 (q : Pattern) (ha : d94611 q = 1) (hb : d122306 q = 1) : d125272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94611, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94611, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94612 q = 1) (hb : d122306 q = 1) : d125273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94612, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94612, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94613 q = 1) (hb : d122306 q = 1) : d125274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94613, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94613, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94614 q = 1) (hb : d122306 q = 1) : d125275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94614, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94614, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94625 q = 1) (hb : d122306 q = 1) : d125286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94625, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94625, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22428 q ha hb
  have h11 (q : Pattern) (ha : d94626 q = 1) (hb : d122306 q = 1) : d125287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94626, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94626, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94627 q = 1) (hb : d122306 q = 1) : d125288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94627, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94627, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94628 q = 1) (hb : d122306 q = 1) : d125289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94628, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94628, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94629 q = 1) (hb : d122306 q = 1) : d125290 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94629, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94629, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94630 q = 1) (hb : d122306 q = 1) : d125291 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94630, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94630, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22430 (p : Pattern) (ha : d94636 p = 1) (hb : d122306 p = 1) : d125297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94631 q = 1) (hb : d122306 q = 1) : d125292 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94631, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94631, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22429 q ha hb
  have h2 (q : Pattern) (ha : d94632 q = 1) (hb : d122306 q = 1) : d125293 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94632, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94632, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94633 q = 1) (hb : d122306 q = 1) : d125294 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94633, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94633, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94634 q = 1) (hb : d122306 q = 1) : d125295 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94634, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94634, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94635 q = 1) (hb : d122306 q = 1) : d125296 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94635, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94635, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94636 q = 1) (hb : d122306 q = 1) : d125297 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94636, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94636, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22431 (p : Pattern) (ha : d94642 p = 1) (hb : d122306 p = 1) : d125303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8927 q = 1) (hb : d122306 q = 1) : d124712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22032 q ha hb
    | true =>
      simp only [d8927, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22020 q ha hb
  have h2 (q : Pattern) (ha : d8928 q = 1) (hb : d122306 q = 1) : d124713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8929 q = 1) (hb : d122306 q = 1) : d124714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8929, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8930 q = 1) (hb : d122306 q = 1) : d124715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8931 q = 1) (hb : d122306 q = 1) : d124716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94642 q = 1) (hb : d122306 q = 1) : d125303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94642, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94642, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22432 (p : Pattern) (ha : d94651 p = 1) (hb : d122306 p = 1) : d125312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d122306 q = 1) : d124872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22063 q ha hb
    | true =>
      simp only [d9051, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d122306 q = 1) : d124873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d122306 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22025 q ha hb
    | true =>
      simp only [d1908, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d122306 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94648 q = 1) (hb : d122306 q = 1) : d125309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94648, d125309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94648, d125309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94649 q = 1) (hb : d122306 q = 1) : d125310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94649, d125310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94649, d125310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94650 q = 1) (hb : d122306 q = 1) : d125311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94650, d125311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94650, d125311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94651 q = 1) (hb : d122306 q = 1) : d125312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94651, d125312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94651, d125312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22433 (p : Pattern) (ha : d94657 p = 1) (hb : d122306 p = 1) : d125318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94652 q = 1) (hb : d122306 q = 1) : d125313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94652, d125313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22432 q ha hb
    | true =>
      simp only [d94652, d125313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22026 q ha hb
  have h2 (q : Pattern) (ha : d94653 q = 1) (hb : d122306 q = 1) : d125314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94653, d125314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94653, d125314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94654 q = 1) (hb : d122306 q = 1) : d125315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94654, d125315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94654, d125315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94655 q = 1) (hb : d122306 q = 1) : d125316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94655, d125316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94655, d125316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94656 q = 1) (hb : d122306 q = 1) : d125317 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94656, d125317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94656, d125317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94657 q = 1) (hb : d122306 q = 1) : d125318 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94657, d125318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94657, d125318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22434 (p : Pattern) (ha : d94663 p = 1) (hb : d122306 p = 1) : d125324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d122306 q = 1) : d124718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22031 q ha hb
    | true =>
      simp only [d8933, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22033 q ha hb
  have h2 (q : Pattern) (ha : d8934 q = 1) (hb : d122306 q = 1) : d124719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94640 q = 1) (hb : d122306 q = 1) : d125301 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94640, d125301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94640, d125301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94641 q = 1) (hb : d122306 q = 1) : d125302 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94641, d125302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94641, d125302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94643 q = 1) (hb : d122306 q = 1) : d125304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94643, d125304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94643, d125304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22431 q ha hb
  have h6 (q : Pattern) (ha : d94644 q = 1) (hb : d122306 q = 1) : d125305 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94644, d125305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94644, d125305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94645 q = 1) (hb : d122306 q = 1) : d125306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94645, d125306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94645, d125306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94646 q = 1) (hb : d122306 q = 1) : d125307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94646, d125307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94646, d125307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94647 q = 1) (hb : d122306 q = 1) : d125308 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94647, d125308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94647, d125308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94658 q = 1) (hb : d122306 q = 1) : d125319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94658, d125319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94658, d125319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22433 q ha hb
  have h11 (q : Pattern) (ha : d94659 q = 1) (hb : d122306 q = 1) : d125320 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94659, d125320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94659, d125320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94660 q = 1) (hb : d122306 q = 1) : d125321 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94660, d125321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94660, d125321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94661 q = 1) (hb : d122306 q = 1) : d125322 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94661, d125322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94661, d125322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94662 q = 1) (hb : d122306 q = 1) : d125323 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94662, d125323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94662, d125323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94663 q = 1) (hb : d122306 q = 1) : d125324 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94663, d125324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94663, d125324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22435 (p : Pattern) (ha : d94669 p = 1) (hb : d122306 p = 1) : d125330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94664 q = 1) (hb : d122306 q = 1) : d125325 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94664, d125325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94664, d125325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22434 q ha hb
  have h2 (q : Pattern) (ha : d94665 q = 1) (hb : d122306 q = 1) : d125326 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94665, d125326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94665, d125326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94666 q = 1) (hb : d122306 q = 1) : d125327 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94666, d125327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94666, d125327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94667 q = 1) (hb : d122306 q = 1) : d125328 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94667, d125328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94667, d125328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94668 q = 1) (hb : d122306 q = 1) : d125329 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94668, d125329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94668, d125329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94669 q = 1) (hb : d122306 q = 1) : d125330 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94669, d125330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94669, d125330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22436 (p : Pattern) (ha : d94676 p = 1) (hb : d122306 p = 1) : d125337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9096 q = 1) (hb : d122306 q = 1) : d124947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22084 q ha hb
    | true =>
      simp only [d9096, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22072 q ha hb
  have h2 (q : Pattern) (ha : d9097 q = 1) (hb : d122306 q = 1) : d124948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9098 q = 1) (hb : d122306 q = 1) : d124949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9098, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9099 q = 1) (hb : d122306 q = 1) : d124950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9100 q = 1) (hb : d122306 q = 1) : d124951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94676 q = 1) (hb : d122306 q = 1) : d125337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94676, d125337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94676, d125337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22437 (p : Pattern) (ha : d94685 p = 1) (hb : d122306 p = 1) : d125346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d122306 q = 1) : d125105 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22115 q ha hb
    | true =>
      simp only [d9220, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d122306 q = 1) : d125106 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d122306 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22077 q ha hb
    | true =>
      simp only [d2386, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d122306 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94682 q = 1) (hb : d122306 q = 1) : d125343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94682, d125343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94682, d125343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94683 q = 1) (hb : d122306 q = 1) : d125344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94683, d125344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94683, d125344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94684 q = 1) (hb : d122306 q = 1) : d125345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94684, d125345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94684, d125345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94685 q = 1) (hb : d122306 q = 1) : d125346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94685, d125346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94685, d125346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro22438 (p : Pattern) (ha : d94691 p = 1) (hb : d122306 p = 1) : d125352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94686 q = 1) (hb : d122306 q = 1) : d125347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94686, d125347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22437 q ha hb
    | true =>
      simp only [d94686, d125347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22078 q ha hb
  have h2 (q : Pattern) (ha : d94687 q = 1) (hb : d122306 q = 1) : d125348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94687, d125348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94687, d125348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94688 q = 1) (hb : d122306 q = 1) : d125349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94688, d125349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94688, d125349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94689 q = 1) (hb : d122306 q = 1) : d125350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94689, d125350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94689, d125350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94690 q = 1) (hb : d122306 q = 1) : d125351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94690, d125351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94690, d125351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94691 q = 1) (hb : d122306 q = 1) : d125352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94691, d125352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94691, d125352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22439 (p : Pattern) (ha : d94697 p = 1) (hb : d122306 p = 1) : d125358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d122306 q = 1) : d124953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22083 q ha hb
    | true =>
      simp only [d9102, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22085 q ha hb
  have h2 (q : Pattern) (ha : d9103 q = 1) (hb : d122306 q = 1) : d124954 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94674 q = 1) (hb : d122306 q = 1) : d125335 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94674, d125335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94674, d125335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94675 q = 1) (hb : d122306 q = 1) : d125336 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94675, d125336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94675, d125336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94677 q = 1) (hb : d122306 q = 1) : d125338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94677, d125338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94677, d125338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22436 q ha hb
  have h6 (q : Pattern) (ha : d94678 q = 1) (hb : d122306 q = 1) : d125339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94678, d125339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94678, d125339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94679 q = 1) (hb : d122306 q = 1) : d125340 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94679, d125340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94679, d125340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94680 q = 1) (hb : d122306 q = 1) : d125341 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94680, d125341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94680, d125341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94681 q = 1) (hb : d122306 q = 1) : d125342 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94681, d125342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94681, d125342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94692 q = 1) (hb : d122306 q = 1) : d125353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94692, d125353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94692, d125353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22438 q ha hb
  have h11 (q : Pattern) (ha : d94693 q = 1) (hb : d122306 q = 1) : d125354 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94693, d125354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94693, d125354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94694 q = 1) (hb : d122306 q = 1) : d125355 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94694, d125355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94694, d125355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94695 q = 1) (hb : d122306 q = 1) : d125356 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94695, d125356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94695, d125356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94696 q = 1) (hb : d122306 q = 1) : d125357 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94696, d125357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94696, d125357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94697 q = 1) (hb : d122306 q = 1) : d125358 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94697, d125358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94697, d125358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro22440 (p : Pattern) (ha : d94703 p = 1) (hb : d122306 p = 1) : d125364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94698 q = 1) (hb : d122306 q = 1) : d125359 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94698, d125359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94698, d125359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22439 q ha hb
  have h2 (q : Pattern) (ha : d94699 q = 1) (hb : d122306 q = 1) : d125360 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94699, d125360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94699, d125360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94700 q = 1) (hb : d122306 q = 1) : d125361 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94700, d125361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94700, d125361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94701 q = 1) (hb : d122306 q = 1) : d125362 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94701, d125362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94701, d125362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94702 q = 1) (hb : d122306 q = 1) : d125363 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94702, d125363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94702, d125363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94703 q = 1) (hb : d122306 q = 1) : d125364 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94703, d125364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94703, d125364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22441 (p : Pattern) (ha : d94709 p = 1) (hb : d122306 p = 1) : d125370 p = 1 := by
  have h0 (q : Pattern) (ha : d94574 q = 1) (hb : d122306 q = 1) : d125239 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94574, d125239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22415 q ha hb
    | true =>
      simp only [d94574, d125239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22420 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94605 q = 1) (hb : d122306 q = 1) : d125266 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94605, d125266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94605, d125266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22425 q ha hb
  have h3 (q : Pattern) (ha : d94606 q = 1) (hb : d122306 q = 1) : d125267 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94606, d125267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94606, d125267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94637 q = 1) (hb : d122306 q = 1) : d125298 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94637, d125298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94637, d125298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22430 q ha hb
  have h5 (q : Pattern) (ha : d94638 q = 1) (hb : d122306 q = 1) : d125299 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94638, d125299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94638, d125299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94639 q = 1) (hb : d122306 q = 1) : d125300 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94639, d125300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94639, d125300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94670 q = 1) (hb : d122306 q = 1) : d125331 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94670, d125331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94670, d125331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22435 q ha hb
  have h8 (q : Pattern) (ha : d94671 q = 1) (hb : d122306 q = 1) : d125332 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94671, d125332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94671, d125332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94672 q = 1) (hb : d122306 q = 1) : d125333 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94672, d125333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94672, d125333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94673 q = 1) (hb : d122306 q = 1) : d125334 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94673, d125334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94673, d125334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94704 q = 1) (hb : d122306 q = 1) : d125365 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94704, d125365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94704, d125365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22440 q ha hb
  have h12 (q : Pattern) (ha : d94705 q = 1) (hb : d122306 q = 1) : d125366 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94705, d125366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94705, d125366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94706 q = 1) (hb : d122306 q = 1) : d125367 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94706, d125367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94706, d125367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94707 q = 1) (hb : d122306 q = 1) : d125368 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94707, d125368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94707, d125368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94708 q = 1) (hb : d122306 q = 1) : d125369 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94708, d125369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94708, d125369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94709 q = 1) (hb : d122306 q = 1) : d125370 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94709, d125370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94709, d125370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro22442 (p : Pattern) (ha : d94715 p = 1) (hb : d122306 p = 1) : d125376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94710 q = 1) (hb : d122306 q = 1) : d125371 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94710, d125371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22441 q ha hb
    | true =>
      simp only [d94710, d125371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94711 q = 1) (hb : d122306 q = 1) : d125372 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94711, d125372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94711, d125372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94712 q = 1) (hb : d122306 q = 1) : d125373 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94712, d125373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94712, d125373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94713 q = 1) (hb : d122306 q = 1) : d125374 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94713, d125374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94713, d125374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94714 q = 1) (hb : d122306 q = 1) : d125375 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94714, d125375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94714, d125375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94715 q = 1) (hb : d122306 q = 1) : d125376 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94715, d125376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94715, d125376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22443 (p : Pattern) (ha : d94721 p = 1) (hb : d122306 p = 1) : d125382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94716 q = 1) (hb : d122306 q = 1) : d125377 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94716, d125377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22442 q ha hb
    | true =>
      simp only [d94716, d125377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94717 q = 1) (hb : d122306 q = 1) : d125378 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94717, d125378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94717, d125378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94718 q = 1) (hb : d122306 q = 1) : d125379 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94718, d125379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94718, d125379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94719 q = 1) (hb : d122306 q = 1) : d125380 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94719, d125380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94719, d125380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94720 q = 1) (hb : d122306 q = 1) : d125381 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94720, d125381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94720, d125381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94721 q = 1) (hb : d122306 q = 1) : d125382 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94721, d125382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94721, d125382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22444 (p : Pattern) (ha : d94727 p = 1) (hb : d122306 p = 1) : d125388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94722 q = 1) (hb : d122306 q = 1) : d125383 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94722, d125383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22443 q ha hb
    | true =>
      simp only [d94722, d125383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94723 q = 1) (hb : d122306 q = 1) : d125384 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94723, d125384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94723, d125384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94724 q = 1) (hb : d122306 q = 1) : d125385 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94724, d125385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94724, d125385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94725 q = 1) (hb : d122306 q = 1) : d125386 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94725, d125386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94725, d125386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94726 q = 1) (hb : d122306 q = 1) : d125387 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94726, d125387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94726, d125387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94727 q = 1) (hb : d122306 q = 1) : d125388 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94727, d125388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94727, d125388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22445 (p : Pattern) (ha : d94733 p = 1) (hb : d122306 p = 1) : d125394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94728 q = 1) (hb : d122306 q = 1) : d125389 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94728, d125389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22444 q ha hb
    | true =>
      simp only [d94728, d125389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94729 q = 1) (hb : d122306 q = 1) : d125390 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94729, d125390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94729, d125390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94730 q = 1) (hb : d122306 q = 1) : d125391 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94730, d125391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94730, d125391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94731 q = 1) (hb : d122306 q = 1) : d125392 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94731, d125392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94731, d125392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94732 q = 1) (hb : d122306 q = 1) : d125393 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94732, d125393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94732, d125393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94733 q = 1) (hb : d122306 q = 1) : d125394 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94733, d125394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94733, d125394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22446 (p : Pattern) (ha : d94739 p = 1) (hb : d122306 p = 1) : d125400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94734 q = 1) (hb : d122306 q = 1) : d125395 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94734, d125395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22445 q ha hb
    | true =>
      simp only [d94734, d125395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94735 q = 1) (hb : d122306 q = 1) : d125396 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94735, d125396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94735, d125396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94736 q = 1) (hb : d122306 q = 1) : d125397 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94736, d125397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94736, d125397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94737 q = 1) (hb : d122306 q = 1) : d125398 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94737, d125398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94737, d125398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94738 q = 1) (hb : d122306 q = 1) : d125399 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94738, d125399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94738, d125399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94739 q = 1) (hb : d122306 q = 1) : d125400 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94739, d125400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94739, d125400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22447 (p : Pattern) (ha : d94745 p = 1) (hb : d122306 p = 1) : d125406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94740 q = 1) (hb : d122306 q = 1) : d125401 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94740, d125401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22446 q ha hb
    | true =>
      simp only [d94740, d125401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94741 q = 1) (hb : d122306 q = 1) : d125402 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94741, d125402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94741, d125402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94742 q = 1) (hb : d122306 q = 1) : d125403 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94742, d125403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94742, d125403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94743 q = 1) (hb : d122306 q = 1) : d125404 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94743, d125404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94743, d125404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94744 q = 1) (hb : d122306 q = 1) : d125405 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94744, d125405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94744, d125405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94745 q = 1) (hb : d122306 q = 1) : d125406 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94745, d125406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94745, d125406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22448 (p : Pattern) (ha : d94751 p = 1) (hb : d122306 p = 1) : d125412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94746 q = 1) (hb : d122306 q = 1) : d125407 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94746, d125407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22447 q ha hb
    | true =>
      simp only [d94746, d125407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94747 q = 1) (hb : d122306 q = 1) : d125408 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94747, d125408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94747, d125408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94748 q = 1) (hb : d122306 q = 1) : d125409 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94748, d125409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94748, d125409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94749 q = 1) (hb : d122306 q = 1) : d125410 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94749, d125410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94749, d125410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94750 q = 1) (hb : d122306 q = 1) : d125411 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94750, d125411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94750, d125411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94751 q = 1) (hb : d122306 q = 1) : d125412 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94751, d125412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94751, d125412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro22449 (p : Pattern) (ha : d104 p = 1) (hb : d122326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d122322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d122322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d122322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d122323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d122323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d122323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d122324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d122324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d122324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d122325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d122325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d122325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d122326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d122326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d122326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22450 (p : Pattern) (ha : d111 p = 1) (hb : d122333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d122322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d122322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d122322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d122323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d122323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d122323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d122324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d122324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d122324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d122325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d122325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d122325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d122329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d122329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d122329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d122330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d122330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d122330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d122331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d122331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d122331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d122332 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d122332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d122332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d122333 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d122333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d122333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22451 (p : Pattern) (ha : d406 p = 1) (hb : d122340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d122329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d122329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d122329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d122330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d122330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d122330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d122338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d122338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d122338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d122339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d122339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d122339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d122340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d122340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d122340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22452 (p : Pattern) (ha : d462 p = 1) (hb : d122365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d122361 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d122361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d122361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d122362 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d122362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d122362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d122363 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d122363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d122363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d122364 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d122364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d122364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d122365 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d122365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d122365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22453 (p : Pattern) (ha : d53647 p = 1) (hb : d122371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d122334 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d122334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22449 q ha hb
    | true =>
      simp only [d112, d122334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22450 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d122335 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d122335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d122335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d122336 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d122336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d122336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d122337 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d122337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d122337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d122341 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d122341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d122341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22451 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d122342 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d122342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d122342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d122343 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d122343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d122343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d122344 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d122344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d122344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d122345 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d122345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d122345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d122366 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d122366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d122366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22452 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d122367 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d122367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d122367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d122368 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d122368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d122368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d122369 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d122369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d122369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d122370 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d122370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d122370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d122371 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d122371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d122371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro22454 (p : Pattern) (ha : d122430 p = 1) (hb : d123951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122321 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
    | true =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d122420 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122420, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122427 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122427, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122428 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122428, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122429 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122429, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122430 q = 1) (hb : d123951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122430, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122430, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22455 (p : Pattern) (ha : d122449 p = 1) (hb : d123958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122321 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22130 q ha hb
    | true =>
      simp only [d122321, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d122420 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122420, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122427 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122427, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122428 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122428, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122429 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122429, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122439 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122328 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22132 q ha hb
    | true =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d122442 q = 1) (hb : d123954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122442, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122446 q = 1) (hb : d123955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122446, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122447 q = 1) (hb : d123956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122447, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122447, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122448 q = 1) (hb : d123957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122448, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122448, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122449 q = 1) (hb : d123958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122449, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122449, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22456 (p : Pattern) (ha : d122458 p = 1) (hb : d125190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122328 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22132 q ha hb
    | true =>
      simp only [d122328, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d122442 q = 1) (hb : d123954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122442, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122446 q = 1) (hb : d123955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122446, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122456 q = 1) (hb : d123956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122456, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122456, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122457 q = 1) (hb : d123957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122457, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122457, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122458 q = 1) (hb : d125190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122458, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122458, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22457 (p : Pattern) (ha : d122490 p = 1) (hb : d125200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122360 q = 1) (hb : d123930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122360, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22137 q ha hb
    | true =>
      simp only [d122360, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d122480 q = 1) (hb : d125196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122480, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122480, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122486 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122487 q = 1) (hb : d125197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122487, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122487, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122488 q = 1) (hb : d125198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122488, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122488, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122489 q = 1) (hb : d125199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122489, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122489, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122490 q = 1) (hb : d125200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122490, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122490, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22458 (p : Pattern) (ha : d122496 p = 1) (hb : d125206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122450 q = 1) (hb : d123959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122450, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22454 q ha hb
    | true =>
      simp only [d122450, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22455 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122453 q = 1) (hb : d123960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122453, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122453, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122454 q = 1) (hb : d125188 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122454, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122454, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122455 q = 1) (hb : d125189 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122455, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122455, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122459 q = 1) (hb : d125191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122459, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122459, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22456 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122460 q = 1) (hb : d125192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122460, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122460, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122461 q = 1) (hb : d125193 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122461, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122461, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122462 q = 1) (hb : d125194 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122462, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122462, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122463 q = 1) (hb : d125195 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122463, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122463, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122491 q = 1) (hb : d125201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122491, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122491, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22457 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122492 q = 1) (hb : d125202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122492, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122492, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122493 q = 1) (hb : d125203 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122493, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122493, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122494 q = 1) (hb : d125204 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122494, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122494, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122495 q = 1) (hb : d125205 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122495, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122495, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122496 q = 1) (hb : d125206 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122496, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122496, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22459 (p : Pattern) (ha : d122502 p = 1) (hb : d125212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d122372 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22453 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d122373 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d122374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d122375 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d122376 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122497 q = 1) (hb : d125207 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122497, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122497, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22458 q ha hb
  have h8 (q : Pattern) (ha : d122498 q = 1) (hb : d125208 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122498, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122498, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122499 q = 1) (hb : d125209 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122499, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122499, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122500 q = 1) (hb : d125210 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122500, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122500, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122501 q = 1) (hb : d125211 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122501, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122501, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122502 q = 1) (hb : d125212 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122502, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122502, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro22460 (p : Pattern) (ha : d122586 p = 1) (hb : d124086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122520 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22165 q ha hb
    | true =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
  have h5 (q : Pattern) (ha : d122576 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122576, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122583 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122583, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122584 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122584, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122585 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122585, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122586 q = 1) (hb : d124086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122586, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122586, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22461 (p : Pattern) (ha : d122607 p = 1) (hb : d124096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122520 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22165 q ha hb
    | true =>
      simp only [d122520, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22166 q ha hb
  have h4 (q : Pattern) (ha : d122576 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122576, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122583 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122583, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122584 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122584, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122585 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122585, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122592 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122597 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122530 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22168 q ha hb
    | true =>
      simp only [d122530, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22169 q ha hb
  have h13 (q : Pattern) (ha : d122600 q = 1) (hb : d124092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122600, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122604 q = 1) (hb : d124093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122604, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122605 q = 1) (hb : d124094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122605, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122605, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122606 q = 1) (hb : d124095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122606, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122606, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122607 q = 1) (hb : d124096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122607, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122607, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22462 (p : Pattern) (ha : d122627 p = 1) (hb : d125215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122530 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22168 q ha hb
    | true =>
      simp only [d122530, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22169 q ha hb
  have h3 (q : Pattern) (ha : d122600 q = 1) (hb : d124092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122600, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122604 q = 1) (hb : d124093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122604, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122625 q = 1) (hb : d124094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122625, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122625, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122626 q = 1) (hb : d124095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122626, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122626, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122627 q = 1) (hb : d125215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122627, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122627, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22463 (p : Pattern) (ha : d122683 p = 1) (hb : d125226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122667 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122672 q = 1) (hb : d125221 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122672, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22196 q ha hb
    | true =>
      simp only [d122672, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22199 q ha hb
  have h3 (q : Pattern) (ha : d122673 q = 1) (hb : d125222 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122673, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122673, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122679 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122680 q = 1) (hb : d125223 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122680, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122680, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122681 q = 1) (hb : d125224 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122681, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122681, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122682 q = 1) (hb : d125225 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122682, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122682, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122683 q = 1) (hb : d125226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122683, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122683, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22464 (p : Pattern) (ha : d122696 p = 1) (hb : d125232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122538 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122608 q = 1) (hb : d124097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122608, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22460 q ha hb
    | true =>
      simp only [d122608, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22461 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122621 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122622 q = 1) (hb : d124098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122622, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122622, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122623 q = 1) (hb : d125213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122623, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122623, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122624 q = 1) (hb : d125214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122624, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122624, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122628 q = 1) (hb : d125216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122628, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122628, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22462 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122630 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122631 q = 1) (hb : d125217 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122631, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122631, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122632 q = 1) (hb : d125218 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122632, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122632, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122633 q = 1) (hb : d125219 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122633, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122633, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122634 q = 1) (hb : d125220 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122634, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122634, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122684 q = 1) (hb : d125227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122684, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122684, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22463 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122691 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122692 q = 1) (hb : d125228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122692, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122692, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122693 q = 1) (hb : d125229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122693, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122693, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122694 q = 1) (hb : d125230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122694, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122694, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122695 q = 1) (hb : d125231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122695, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122695, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122696 q = 1) (hb : d125232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122696, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122696, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22465 (p : Pattern) (ha : d122702 p = 1) (hb : d125238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122697 q = 1) (hb : d125233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122697, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122697, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22464 q ha hb
  have h2 (q : Pattern) (ha : d122698 q = 1) (hb : d125234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122698, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122698, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122699 q = 1) (hb : d125235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122699, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122699, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122700 q = 1) (hb : d125236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122700, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122700, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122701 q = 1) (hb : d125237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122701, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122701, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122702 q = 1) (hb : d125238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122702, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122702, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22466 (p : Pattern) (ha : d122797 p = 1) (hb : d124272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122729 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22206 q ha hb
    | true =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
  have h5 (q : Pattern) (ha : d122787 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122787, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122794 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122794, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122795 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122795, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122796 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122796, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122797 q = 1) (hb : d124272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122797, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122797, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22467 (p : Pattern) (ha : d122818 p = 1) (hb : d124282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122729 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22206 q ha hb
    | true =>
      simp only [d122729, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22207 q ha hb
  have h4 (q : Pattern) (ha : d122787 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122787, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122794 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122794, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122795 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122795, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122796 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122796, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122803 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122808 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122739 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22209 q ha hb
    | true =>
      simp only [d122739, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22210 q ha hb
  have h13 (q : Pattern) (ha : d122811 q = 1) (hb : d124278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122811, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122815 q = 1) (hb : d124279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122815, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122816 q = 1) (hb : d124280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122816, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122816, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122817 q = 1) (hb : d124281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122817, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122817, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122818 q = 1) (hb : d124282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122818, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122818, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22468 (p : Pattern) (ha : d122838 p = 1) (hb : d125242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122739 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22209 q ha hb
    | true =>
      simp only [d122739, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22210 q ha hb
  have h3 (q : Pattern) (ha : d122811 q = 1) (hb : d124278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122811, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122815 q = 1) (hb : d124279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122815, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122836 q = 1) (hb : d124280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122836, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122836, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122837 q = 1) (hb : d124281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122837, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122837, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122838 q = 1) (hb : d125242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122838, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122838, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22469 (p : Pattern) (ha : d122906 p = 1) (hb : d125253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122895 q = 1) (hb : d125248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122895, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22238 q ha hb
    | true =>
      simp only [d122895, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22241 q ha hb
  have h3 (q : Pattern) (ha : d122896 q = 1) (hb : d125249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122896, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122896, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122903 q = 1) (hb : d125250 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122903, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122903, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122904 q = 1) (hb : d125251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122904, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122904, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122905 q = 1) (hb : d125252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122905, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122905, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122906 q = 1) (hb : d125253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122906, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122906, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22470 (p : Pattern) (ha : d122919 p = 1) (hb : d125259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122819 q = 1) (hb : d124283 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122819, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22466 q ha hb
    | true =>
      simp only [d122819, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22467 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122833 q = 1) (hb : d124284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122833, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122833, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122834 q = 1) (hb : d125240 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122834, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122834, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122835 q = 1) (hb : d125241 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122835, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122835, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122839 q = 1) (hb : d125243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122839, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122839, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22468 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122841 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122842 q = 1) (hb : d125244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122842, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122842, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122843 q = 1) (hb : d125245 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122843, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122843, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122844 q = 1) (hb : d125246 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122844, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122844, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122845 q = 1) (hb : d125247 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122845, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122845, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122907 q = 1) (hb : d125254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122907, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122907, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22469 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122914 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122915 q = 1) (hb : d125255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122915, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122915, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122916 q = 1) (hb : d125256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122916, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122916, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122917 q = 1) (hb : d125257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122917, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122917, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122918 q = 1) (hb : d125258 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122918, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122918, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122919 q = 1) (hb : d125259 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122919, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122919, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22471 (p : Pattern) (ha : d122925 p = 1) (hb : d125265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122920 q = 1) (hb : d125260 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122920, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122920, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22470 q ha hb
  have h2 (q : Pattern) (ha : d122921 q = 1) (hb : d125261 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122921, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122921, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122922 q = 1) (hb : d125262 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122922, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122922, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122923 q = 1) (hb : d125263 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122923, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122923, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122924 q = 1) (hb : d125264 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122924, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122924, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122925 q = 1) (hb : d125265 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122925, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122925, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22472 (p : Pattern) (ha : d123056 p = 1) (hb : d124473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122970 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22250 q ha hb
    | true =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
  have h5 (q : Pattern) (ha : d123038 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123038, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123053 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123053, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123054 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123054, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123055 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123055, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123056 q = 1) (hb : d124473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123056, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123056, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22473 (p : Pattern) (ha : d123078 p = 1) (hb : d124483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122970 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22250 q ha hb
    | true =>
      simp only [d122970, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22251 q ha hb
  have h4 (q : Pattern) (ha : d123038 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123038, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123053 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123053, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123054 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123054, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123055 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123055, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123062 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123067 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122980 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22253 q ha hb
    | true =>
      simp only [d122980, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22254 q ha hb
  have h13 (q : Pattern) (ha : d123071 q = 1) (hb : d124479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123071, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123075 q = 1) (hb : d124480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123075, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123076 q = 1) (hb : d124481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123076, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123076, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123077 q = 1) (hb : d124482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123077, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123077, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123078 q = 1) (hb : d124483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123078, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123078, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22474 (p : Pattern) (ha : d123103 p = 1) (hb : d125270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122980 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22253 q ha hb
    | true =>
      simp only [d122980, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22254 q ha hb
  have h3 (q : Pattern) (ha : d123071 q = 1) (hb : d124479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123071, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123075 q = 1) (hb : d124480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123075, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123101 q = 1) (hb : d124481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123101, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123101, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123102 q = 1) (hb : d124482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123102, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123102, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123103 q = 1) (hb : d125270 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123103, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123103, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22475 (p : Pattern) (ha : d123182 p = 1) (hb : d124637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123141 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22282 q ha hb
    | true =>
      simp only [d123141, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
  have h2 (q : Pattern) (ha : d123142 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123143 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123153 q = 1) (hb : d124605 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123153, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123168 q = 1) (hb : d124622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123168, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22283 q ha hb
    | true =>
      simp only [d123168, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22288 q hb ha
  have h7 (q : Pattern) (ha : d123169 q = 1) (hb : d124623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123169, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123169, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123170 q = 1) (hb : d124624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123170, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123170, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123171 q = 1) (hb : d124625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123171, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123171, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123181 q = 1) (hb : d124636 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123181, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123181, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123182 q = 1) (hb : d124637 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123182, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123182, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22476 (p : Pattern) (ha : d123188 p = 1) (hb : d125279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123183 q = 1) (hb : d124638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123183, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22475 q ha hb
    | true =>
      simp only [d123183, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123184 q = 1) (hb : d124639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123184, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123184, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123174 q = 1) (hb : d124628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22289 q ha hb
    | true =>
      simp only [d123174, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123175 q = 1) (hb : d124629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123175, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123185 q = 1) (hb : d125276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123185, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123185, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123186 q = 1) (hb : d125277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123186, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123186, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123187 q = 1) (hb : d125278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123187, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123187, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123188 q = 1) (hb : d125279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123188, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123188, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22477 (p : Pattern) (ha : d123212 p = 1) (hb : d125285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123180 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123193 q = 1) (hb : d125280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123193, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22476 q ha hb
    | true =>
      simp only [d123193, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22294 q ha hb
  have h3 (q : Pattern) (ha : d123194 q = 1) (hb : d125281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123194, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123194, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123208 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123209 q = 1) (hb : d125282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123209, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123209, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123210 q = 1) (hb : d125283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123210, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123210, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123211 q = 1) (hb : d125284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123211, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123211, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123212 q = 1) (hb : d125285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123212, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123212, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22478 (p : Pattern) (ha : d123225 p = 1) (hb : d125291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123079 q = 1) (hb : d124484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123079, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22472 q ha hb
    | true =>
      simp only [d123079, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22473 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123098 q = 1) (hb : d124485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123098, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123098, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123099 q = 1) (hb : d125268 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123099, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123099, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123100 q = 1) (hb : d125269 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123100, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123100, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123104 q = 1) (hb : d125271 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123104, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123104, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22474 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123106 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123107 q = 1) (hb : d125272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123107, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123107, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123108 q = 1) (hb : d125273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123108, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123108, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123109 q = 1) (hb : d125274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123109, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123109, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123110 q = 1) (hb : d125275 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123110, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123110, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123213 q = 1) (hb : d125286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123213, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123213, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22477 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123220 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123221 q = 1) (hb : d125287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123221, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123221, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123222 q = 1) (hb : d125288 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123222, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123222, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123223 q = 1) (hb : d125289 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123223, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123223, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123224 q = 1) (hb : d125290 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123224, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123224, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123225 q = 1) (hb : d125291 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123225, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123225, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22479 (p : Pattern) (ha : d123231 p = 1) (hb : d125297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123226 q = 1) (hb : d125292 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123226, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123226, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22478 q ha hb
  have h2 (q : Pattern) (ha : d123227 q = 1) (hb : d125293 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123227, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123227, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123228 q = 1) (hb : d125294 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123228, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123228, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123229 q = 1) (hb : d125295 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123229, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123229, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123230 q = 1) (hb : d125296 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123230, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123230, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123231 q = 1) (hb : d125297 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123231, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123231, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22480 (p : Pattern) (ha : d123363 p = 1) (hb : d124707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d123277 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22303 q ha hb
    | true =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
  have h5 (q : Pattern) (ha : d123345 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123345, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123360 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123360, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123361 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123361, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123362 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123362, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123363 q = 1) (hb : d124707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123363, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123363, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22481 (p : Pattern) (ha : d123385 p = 1) (hb : d124717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123277 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22303 q ha hb
    | true =>
      simp only [d123277, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22304 q ha hb
  have h4 (q : Pattern) (ha : d123345 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123345, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123360 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123360, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123361 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123361, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123362 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123362, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123369 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123374 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123287 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22306 q ha hb
    | true =>
      simp only [d123287, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22307 q ha hb
  have h13 (q : Pattern) (ha : d123378 q = 1) (hb : d124713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123378, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123382 q = 1) (hb : d124714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123382, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123383 q = 1) (hb : d124715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123383, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123383, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123384 q = 1) (hb : d124716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123384, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123384, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123385 q = 1) (hb : d124717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123385, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123385, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22482 (p : Pattern) (ha : d123410 p = 1) (hb : d125303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123287 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22306 q ha hb
    | true =>
      simp only [d123287, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22307 q ha hb
  have h3 (q : Pattern) (ha : d123378 q = 1) (hb : d124713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123378, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123382 q = 1) (hb : d124714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123382, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123408 q = 1) (hb : d124715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123408, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123408, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123409 q = 1) (hb : d124716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123409, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123409, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123410 q = 1) (hb : d125303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123410, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123410, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22483 (p : Pattern) (ha : d123489 p = 1) (hb : d124871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123448 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22335 q ha hb
    | true =>
      simp only [d123448, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
  have h2 (q : Pattern) (ha : d123449 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123450 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123459 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123460 q = 1) (hb : d124839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123460, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123475 q = 1) (hb : d124856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123475, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22336 q ha hb
    | true =>
      simp only [d123475, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22341 q hb ha
  have h7 (q : Pattern) (ha : d123476 q = 1) (hb : d124857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123476, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123476, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123477 q = 1) (hb : d124858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123477, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123477, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123478 q = 1) (hb : d124859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123478, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123478, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123488 q = 1) (hb : d124870 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123488, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123488, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123489 q = 1) (hb : d124871 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123489, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123489, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22484 (p : Pattern) (ha : d123495 p = 1) (hb : d125312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123490 q = 1) (hb : d124872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123490, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22483 q ha hb
    | true =>
      simp only [d123490, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123491 q = 1) (hb : d124873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123491, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123491, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123481 q = 1) (hb : d124862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22342 q ha hb
    | true =>
      simp only [d123481, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123482 q = 1) (hb : d124863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123482, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123492 q = 1) (hb : d125309 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123492, d125309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123492, d125309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123493 q = 1) (hb : d125310 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123493, d125310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123493, d125310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123494 q = 1) (hb : d125311 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123494, d125311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123494, d125311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123495 q = 1) (hb : d125312 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123495, d125312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123495, d125312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22485 (p : Pattern) (ha : d123519 p = 1) (hb : d125318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123500 q = 1) (hb : d125313 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123500, d125313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22484 q ha hb
    | true =>
      simp only [d123500, d125313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22347 q ha hb
  have h3 (q : Pattern) (ha : d123501 q = 1) (hb : d125314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123501, d125314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123501, d125314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123516 q = 1) (hb : d125315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123516, d125315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123516, d125315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123517 q = 1) (hb : d125316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123517, d125316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123517, d125316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123518 q = 1) (hb : d125317 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123518, d125317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123518, d125317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123519 q = 1) (hb : d125318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123519, d125318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123519, d125318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22486 (p : Pattern) (ha : d123532 p = 1) (hb : d125324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123386 q = 1) (hb : d124718 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123386, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22480 q ha hb
    | true =>
      simp only [d123386, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22481 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123405 q = 1) (hb : d124719 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123405, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123405, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123406 q = 1) (hb : d125301 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123406, d125301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123406, d125301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123407 q = 1) (hb : d125302 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123407, d125302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123407, d125302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123411 q = 1) (hb : d125304 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123411, d125304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123411, d125304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22482 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123413 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123414 q = 1) (hb : d125305 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123414, d125305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123414, d125305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123415 q = 1) (hb : d125306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123415, d125306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123415, d125306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123416 q = 1) (hb : d125307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123416, d125307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123416, d125307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123417 q = 1) (hb : d125308 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123417, d125308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123417, d125308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123520 q = 1) (hb : d125319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123520, d125319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123520, d125319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22485 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123527 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123528 q = 1) (hb : d125320 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123528, d125320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123528, d125320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123529 q = 1) (hb : d125321 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123529, d125321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123529, d125321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123530 q = 1) (hb : d125322 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123530, d125322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123530, d125322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123531 q = 1) (hb : d125323 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123531, d125323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123531, d125323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123532 q = 1) (hb : d125324 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123532, d125324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123532, d125324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22487 (p : Pattern) (ha : d123538 p = 1) (hb : d125330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123533 q = 1) (hb : d125325 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123533, d125325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123533, d125325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22486 q ha hb
  have h2 (q : Pattern) (ha : d123534 q = 1) (hb : d125326 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123534, d125326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123534, d125326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123535 q = 1) (hb : d125327 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123535, d125327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123535, d125327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123536 q = 1) (hb : d125328 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123536, d125328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123536, d125328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123537 q = 1) (hb : d125329 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123537, d125329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123537, d125329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123538 q = 1) (hb : d125330 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123538, d125330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123538, d125330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22488 (p : Pattern) (ha : d123665 p = 1) (hb : d124942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d123583 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22356 q ha hb
    | true =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h5 (q : Pattern) (ha : d123647 q = 1) (hb : d124938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123647, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123662 q = 1) (hb : d124939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123662, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123663 q = 1) (hb : d124940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123663, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123664 q = 1) (hb : d124941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123664, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123665 q = 1) (hb : d124942 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123665, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123665, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro22489 (p : Pattern) (ha : d123687 p = 1) (hb : d124952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123583 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22356 q ha hb
    | true =>
      simp only [d123583, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22357 q ha hb
  have h4 (q : Pattern) (ha : d123647 q = 1) (hb : d124938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123647, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123662 q = 1) (hb : d124939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123662, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123663 q = 1) (hb : d124940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123663, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123664 q = 1) (hb : d124941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123664, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123676 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123593 q = 1) (hb : d124947 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22359 q ha hb
    | true =>
      simp only [d123593, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22360 q ha hb
  have h13 (q : Pattern) (ha : d123680 q = 1) (hb : d124948 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123680, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123684 q = 1) (hb : d124949 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123684, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123685 q = 1) (hb : d124950 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123685, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123685, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123686 q = 1) (hb : d124951 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123686, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123686, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123687 q = 1) (hb : d124952 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123687, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123687, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro22490 (p : Pattern) (ha : d123712 p = 1) (hb : d125337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123593 q = 1) (hb : d124947 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22359 q ha hb
    | true =>
      simp only [d123593, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22360 q ha hb
  have h3 (q : Pattern) (ha : d123680 q = 1) (hb : d124948 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123680, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123684 q = 1) (hb : d124949 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123684, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123710 q = 1) (hb : d124950 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123710, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123710, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123711 q = 1) (hb : d124951 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123711, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123711, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123712 q = 1) (hb : d125337 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123712, d125337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123712, d125337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22491 (p : Pattern) (ha : d123781 p = 1) (hb : d125104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22388 q ha hb
    | true =>
      simp only [d123740, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123752 q = 1) (hb : d125072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123767 q = 1) (hb : d125089 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123767, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22389 q ha hb
    | true =>
      simp only [d123767, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22394 q hb ha
  have h7 (q : Pattern) (ha : d123768 q = 1) (hb : d125090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123768, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123768, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123769 q = 1) (hb : d125091 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123769, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123769, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123770 q = 1) (hb : d125092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123770, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123770, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123780 q = 1) (hb : d125103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123780, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123780, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123781 q = 1) (hb : d125104 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123781, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123781, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro22492 (p : Pattern) (ha : d123787 p = 1) (hb : d125346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123782 q = 1) (hb : d125105 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123782, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22491 q ha hb
    | true =>
      simp only [d123782, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123783 q = 1) (hb : d125106 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123783, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123783, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123773 q = 1) (hb : d125095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22395 q ha hb
    | true =>
      simp only [d123773, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123774 q = 1) (hb : d125096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123784 q = 1) (hb : d125343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123784, d125343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123784, d125343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123785 q = 1) (hb : d125344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123785, d125344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123785, d125344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123786 q = 1) (hb : d125345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123786, d125345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123786, d125345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123787 q = 1) (hb : d125346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123787, d125346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123787, d125346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro22493 (p : Pattern) (ha : d123811 p = 1) (hb : d125352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123792 q = 1) (hb : d125347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123792, d125347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22492 q ha hb
    | true =>
      simp only [d123792, d125347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22400 q ha hb
  have h3 (q : Pattern) (ha : d123793 q = 1) (hb : d125348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123793, d125348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123793, d125348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123808 q = 1) (hb : d125349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123808, d125349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123808, d125349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123809 q = 1) (hb : d125350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123809, d125350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123809, d125350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123810 q = 1) (hb : d125351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123810, d125351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123810, d125351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123811 q = 1) (hb : d125352 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123811, d125352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123811, d125352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro22494 (p : Pattern) (ha : d123824 p = 1) (hb : d125358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123688 q = 1) (hb : d124953 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123688, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22488 q ha hb
    | true =>
      simp only [d123688, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22489 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123706 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123707 q = 1) (hb : d124954 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123707, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123707, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123708 q = 1) (hb : d125335 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123708, d125335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123708, d125335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123709 q = 1) (hb : d125336 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123709, d125336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123709, d125336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123713 q = 1) (hb : d125338 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123713, d125338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123713, d125338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22490 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123715 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123716 q = 1) (hb : d125339 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123716, d125339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123716, d125339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123717 q = 1) (hb : d125340 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123717, d125340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123717, d125340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123718 q = 1) (hb : d125341 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123718, d125341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123718, d125341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123719 q = 1) (hb : d125342 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123719, d125342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123719, d125342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123812 q = 1) (hb : d125353 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123812, d125353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123812, d125353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22493 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123819 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123820 q = 1) (hb : d125354 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123820, d125354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123820, d125354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123821 q = 1) (hb : d125355 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123821, d125355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123821, d125355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123822 q = 1) (hb : d125356 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123822, d125356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123822, d125356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123823 q = 1) (hb : d125357 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123823, d125357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123823, d125357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123824 q = 1) (hb : d125358 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123824, d125358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123824, d125358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro22495 (p : Pattern) (ha : d123830 p = 1) (hb : d125364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123825 q = 1) (hb : d125359 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123825, d125359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123825, d125359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22494 q ha hb
  have h2 (q : Pattern) (ha : d123826 q = 1) (hb : d125360 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123826, d125360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123826, d125360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123827 q = 1) (hb : d125361 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123827, d125361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123827, d125361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123828 q = 1) (hb : d125362 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123828, d125362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123828, d125362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123829 q = 1) (hb : d125363 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123829, d125363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123829, d125363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123830 q = 1) (hb : d125364 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123830, d125364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123830, d125364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro22496 (p : Pattern) (ha : d123836 p = 1) (hb : d125370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d122703 q = 1) (hb : d125239 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122703, d125239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22459 q ha hb
    | true =>
      simp only [d122703, d125239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22465 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122926 q = 1) (hb : d125266 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122926, d125266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122926, d125266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22471 q ha hb
  have h3 (q : Pattern) (ha : d122927 q = 1) (hb : d125267 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d122927, d125267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d122927, d125267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123232 q = 1) (hb : d125298 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123232, d125298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123232, d125298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22479 q ha hb
  have h5 (q : Pattern) (ha : d123233 q = 1) (hb : d125299 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123233, d125299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123233, d125299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123234 q = 1) (hb : d125300 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123234, d125300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123234, d125300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123539 q = 1) (hb : d125331 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123539, d125331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123539, d125331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22487 q ha hb
  have h8 (q : Pattern) (ha : d123540 q = 1) (hb : d125332 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123540, d125332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123540, d125332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123541 q = 1) (hb : d125333 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123541, d125333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123541, d125333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123542 q = 1) (hb : d125334 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123542, d125334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123542, d125334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123831 q = 1) (hb : d125365 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123831, d125365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123831, d125365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22495 q ha hb
  have h12 (q : Pattern) (ha : d123832 q = 1) (hb : d125366 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123832, d125366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123832, d125366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123833 q = 1) (hb : d125367 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123833, d125367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123833, d125367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123834 q = 1) (hb : d125368 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123834, d125368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123834, d125368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123835 q = 1) (hb : d125369 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d123835, d125369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123835, d125369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123836 q = 1) (hb : d125370 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d123836, d125370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123836, d125370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro22497 (p : Pattern) (ha : d123842 p = 1) (hb : d125376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d125371 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d125371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22496 q ha hb
    | true =>
      simp only [d123837, d125371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d125372 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d125372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d125372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d125373 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d125373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d125373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d125374 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d125374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d125374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d125375 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d125375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d125375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d125376 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d125376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d125376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22498 (p : Pattern) (ha : d123848 p = 1) (hb : d125382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d125377 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d125377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22497 q ha hb
    | true =>
      simp only [d123843, d125377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d125378 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d125378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d125378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d125379 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d125379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d125379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d125380 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d125380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d125380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d125381 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d125381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d125381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d125382 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d125382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d125382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro22499 (p : Pattern) (ha : d123854 p = 1) (hb : d125388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d125383 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d125383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22498 q ha hb
    | true =>
      simp only [d123849, d125383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d125384 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d125384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d125384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d125385 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d125385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d125385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d125386 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d125386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d125386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d125387 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d125387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d125387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d125388 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d125388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d125388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
