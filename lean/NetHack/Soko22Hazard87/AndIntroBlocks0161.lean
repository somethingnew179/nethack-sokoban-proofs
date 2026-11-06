import NetHack.Soko22Hazard87.AndIntroBlocks0160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro40250 (p : Pattern) (ha : d128286 p = 1) (hb : d159762 p = 1) : d178392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d159762 q = 1) : d178375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d178375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40247 q ha hb
    | true =>
      simp only [d16331, d178375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40230 q ha hb
  have h2 (q : Pattern) (ha : d128275 q = 1) (hb : d159762 q = 1) : d178376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d178376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d178376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d159762 q = 1) : d178378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d178378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40248 q ha hb
    | true =>
      simp only [d16336, d178378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d159762 q = 1) : d178379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d178379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d178379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d159762 q = 1) : d178380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d178380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d178380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d159762 q = 1) : d178390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d178390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d178390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d159762 q = 1) : d178391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d178391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d178391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d159762 q = 1) : d178392 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d178392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d178392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40251 (p : Pattern) (ha : d16362 p = 1) (hb : d159762 p = 1) : d178399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16359 q = 1) (hb : d100904 q = 1) : d16359 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16360 q = 1) (hb : d159761 q = 1) : d178398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d159761, d178398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16360, d159761, d178398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16361 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16362 q = 1) (hb : d159762 q = 1) : d178399 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d159762, d178399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16362, d159762, d178399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40252 (p : Pattern) (ha : d16363 p = 1) (hb : d159762 p = 1) : d178265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16159 q = 1) (hb : d100904 q = 1) : d16159 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16160 q = 1) (hb : d159761 q = 1) : d178264 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d159761, d178264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16160, d159761, d178264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12862 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16363 q = 1) (hb : d159762 q = 1) : d178265 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d159762, d178265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16363, d159762, d178265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40253 (p : Pattern) (ha : d16367 p = 1) (hb : d159762 p = 1) : d160248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d974 q = 1) (hb : d100904 q = 1) : d974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12862 q = 1) (hb : d159761 q = 1) : d160247 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12862, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16367 q = 1) (hb : d159762 q = 1) : d160248 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16367, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40254 (p : Pattern) (ha : d16377 p = 1) (hb : d159762 p = 1) : d178409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d159762 q = 1) : d178400 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d178400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40251 q ha hb
    | true =>
      simp only [d16364, d178400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40252 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d159762 q = 1) : d178401 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d178401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d178401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d159762 q = 1) : d178402 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d178402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d178402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d159762 q = 1) : d178403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d178403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40252 q ha hb
    | true =>
      simp only [d16368, d178403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40253 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d159762 q = 1) : d178404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d178404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d178404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d159762 q = 1) : d178405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d178405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d178405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d159762 q = 1) : d178406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d178406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d178406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d159762 q = 1) : d178403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d178403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40252 q ha hb
    | true =>
      simp only [d16372, d178403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40222 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d159762 q = 1) : d178404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d178404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d178404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d159762 q = 1) : d178405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d178405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d178405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d159762 q = 1) : d160253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40222 q ha hb
    | true =>
      simp only [d987, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31511 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d159762 q = 1) : d160254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d159762 q = 1) : d160255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16375 q = 1) (hb : d159762 q = 1) : d178407 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d178407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d178407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16376 q = 1) (hb : d159762 q = 1) : d178408 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d178408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d178408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16377 q = 1) (hb : d159762 q = 1) : d178409 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d178409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16377, d178409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40255 (p : Pattern) (ha : d16381 p = 1) (hb : d159762 p = 1) : d178413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d159762 q = 1) : d178403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d178403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40252 q ha hb
    | true =>
      simp only [d16372, d178403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40222 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d159762 q = 1) : d178404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d178404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d178404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d159762 q = 1) : d178405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d178405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d178405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d159762 q = 1) : d160253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40222 q ha hb
    | true =>
      simp only [d987, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31511 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d159762 q = 1) : d160254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d159762 q = 1) : d160255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16375 q = 1) (hb : d159762 q = 1) : d178407 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d178407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d178407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d159762 q = 1) : d160261 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16380 q = 1) (hb : d159762 q = 1) : d178412 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d178412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16380, d178412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16381 q = 1) (hb : d159762 q = 1) : d178413 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d178413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16381, d178413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40256 (p : Pattern) (ha : d16387 p = 1) (hb : d159762 p = 1) : d178419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d159762 q = 1) : d178410 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d178410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40254 q ha hb
    | true =>
      simp only [d16378, d178410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d159762 q = 1) : d178411 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d178411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d178411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d159762 q = 1) : d178414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d178414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40255 q ha hb
    | true =>
      simp only [d16382, d178414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d159762 q = 1) : d178415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d178415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d178415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d159762 q = 1) : d178416 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d178416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d178416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d159762 q = 1) : d178417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d178417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d178417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d159762 q = 1) : d178418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d178418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d178418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d159762 q = 1) : d178419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d178419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d178419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40257 (p : Pattern) (ha : d16391 p = 1) (hb : d159762 p = 1) : d178423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d159762 q = 1) : d178414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d178414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40255 q ha hb
    | true =>
      simp only [d16382, d178414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d159762 q = 1) : d178415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d178415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d178415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d159762 q = 1) : d160272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40223 q ha hb
    | true =>
      simp only [d1006, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d159762 q = 1) : d160273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d159762 q = 1) : d178420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d178420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d178420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d159762 q = 1) : d178421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d178421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d178421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d159762 q = 1) : d178422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d178422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d178422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d159762 q = 1) : d178423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d178423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d178423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40258 (p : Pattern) (ha : d16417 p = 1) (hb : d159762 p = 1) : d178429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d159762 q = 1) : d178414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d178414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40255 q ha hb
    | true =>
      simp only [d16382, d178414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d159762 q = 1) : d178415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d178415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d178415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d159762 q = 1) : d178426 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d178426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d178426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d159762 q = 1) : d178427 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d178427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d178427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d159762 q = 1) : d178428 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d178428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d178428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d159762 q = 1) : d178429 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d178429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d178429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40259 (p : Pattern) (ha : d128296 p = 1) (hb : d159762 p = 1) : d178435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d159762 q = 1) : d178424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d178424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40256 q ha hb
    | true =>
      simp only [d16392, d178424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40257 q ha hb
  have h2 (q : Pattern) (ha : d128292 q = 1) (hb : d159762 q = 1) : d178425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d178425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128292, d178425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d159762 q = 1) : d178430 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d178430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40258 q ha hb
    | true =>
      simp only [d16418, d178430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d159762 q = 1) : d178431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d178431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d178431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d159762 q = 1) : d178432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d178432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d178432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d159762 q = 1) : d178433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d178433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d178433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d159762 q = 1) : d178434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d178434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d178434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d159762 q = 1) : d178435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d178435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d178435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40260 (p : Pattern) (ha : d128302 p = 1) (hb : d159762 p = 1) : d178441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16246 q = 1) (hb : d159762 q = 1) : d178315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16246, d178315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16246, d178315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40229 q ha hb
  have h2 (q : Pattern) (ha : d16247 q = 1) (hb : d159762 q = 1) : d178316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16247, d178316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16247, d178316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16255 q = 1) (hb : d159762 q = 1) : d178324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d178324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40229 q ha hb
    | true =>
      simp only [d16255, d178324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40231 q ha hb
  have h4 (q : Pattern) (ha : d16256 q = 1) (hb : d159762 q = 1) : d178325 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d178325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16256, d178325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16257 q = 1) (hb : d159762 q = 1) : d178326 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16257, d178326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16257, d178326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128280 q = 1) (hb : d159762 q = 1) : d178384 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d178384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40242 q ha hb
    | true =>
      simp only [d128280, d178384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40249 q ha hb
  have h7 (q : Pattern) (ha : d16344 q = 1) (hb : d159762 q = 1) : d178386 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16344, d178386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40232 q ha hb
    | true =>
      simp only [d16344, d178386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40220 q ha hb
  have h8 (q : Pattern) (ha : d128281 q = 1) (hb : d159762 q = 1) : d178387 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d178387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128281, d178387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128282 q = 1) (hb : d159762 q = 1) : d178388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d178388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128282, d178388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128283 q = 1) (hb : d159762 q = 1) : d178389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d178389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128283, d178389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128287 q = 1) (hb : d159762 q = 1) : d178393 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d178393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128287, d178393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40250 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d159762 q = 1) : d160237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d160237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d160237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40221 q ha hb
  have h13 (q : Pattern) (ha : d128288 q = 1) (hb : d159762 q = 1) : d178394 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d178394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128288, d178394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128289 q = 1) (hb : d159762 q = 1) : d178395 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d178395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128289, d178395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128290 q = 1) (hb : d159762 q = 1) : d178396 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d178396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128290, d178396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128291 q = 1) (hb : d159762 q = 1) : d178397 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d178397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128291, d178397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128297 q = 1) (hb : d159762 q = 1) : d178436 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d178436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128297, d178436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40259 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d159762 q = 1) : d160301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d160301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d160301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40225 q ha hb
  have h19 (q : Pattern) (ha : d128298 q = 1) (hb : d159762 q = 1) : d178437 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d178437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128298, d178437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128299 q = 1) (hb : d159762 q = 1) : d178438 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d178438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128299, d178438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128300 q = 1) (hb : d159762 q = 1) : d178439 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d178439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128300, d178439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128301 q = 1) (hb : d159762 q = 1) : d178440 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d178440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128301, d178440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128302 q = 1) (hb : d159762 q = 1) : d178441 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d178441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128302, d178441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40261 (p : Pattern) (ha : d128308 p = 1) (hb : d159762 p = 1) : d178447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d159762 q = 1) : d178442 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d178442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d178442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40260 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d159762 q = 1) : d178443 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d178443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d178443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d159762 q = 1) : d178444 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d178444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d178444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d159762 q = 1) : d178445 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d178445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d178445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d159762 q = 1) : d178446 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d178446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d178446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d159762 q = 1) : d178447 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d178447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d178447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40262 (p : Pattern) (ha : d14773 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5021 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5022 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5022, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14773 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14773, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40263 (p : Pattern) (ha : d14778 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1124 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1127 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1127, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14772 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14778 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14778, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40264 (p : Pattern) (ha : d16442 p = 1) (hb : d159762 p = 1) : d178451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16439 q = 1) (hb : d100904 q = 1) : d16439 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16440 q = 1) (hb : d159761 q = 1) : d178450 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d159761, d178450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16440, d159761, d178450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16441 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16442 q = 1) (hb : d159762 q = 1) : d178451 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d159762, d178451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16442, d159762, d178451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40265 (p : Pattern) (ha : d16443 p = 1) (hb : d159762 p = 1) : d160318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1113 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1124 q = 1) (hb : d100904 q = 1) : d1124 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1125 q = 1) (hb : d159761 q = 1) : d160317 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d159761, d160317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1125, d159761, d160317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16443 q = 1) (hb : d159762 q = 1) : d160318 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d159762, d160318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16443, d159762, d160318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40266 (p : Pattern) (ha : d16456 p = 1) (hb : d159762 p = 1) : d178457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d159762 q = 1) : d178452 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40264 q ha hb
    | true =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d159762 q = 1) : d178453 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d159762 q = 1) : d178454 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
    | true =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40262 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d159762 q = 1) : d178455 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16451 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
    | true =>
      simp only [d16451, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40263 q ha hb
  have h9 (q : Pattern) (ha : d16452 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16453 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16454 q = 1) (hb : d159762 q = 1) : d160326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16454, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16455 q = 1) (hb : d159762 q = 1) : d178456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d178456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16455, d178456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16456 q = 1) (hb : d159762 q = 1) : d178457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d178457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16456, d178457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40267 (p : Pattern) (ha : d16460 p = 1) (hb : d159762 p = 1) : d160332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
    | true =>
      simp only [d16451, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40263 q ha hb
  have h2 (q : Pattern) (ha : d16452 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16453 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16454 q = 1) (hb : d159762 q = 1) : d160326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16454, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16459 q = 1) (hb : d159762 q = 1) : d160331 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d160331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16459, d160331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16460 q = 1) (hb : d159762 q = 1) : d160332 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d160332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16460, d160332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40268 (p : Pattern) (ha : d16466 p = 1) (hb : d159762 p = 1) : d178463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40266 q ha hb
    | true =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d159762 q = 1) : d178461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d159762 q = 1) : d178462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16466 q = 1) (hb : d159762 q = 1) : d178463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16466, d178463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16466, d178463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40269 (p : Pattern) (ha : d16470 p = 1) (hb : d159762 p = 1) : d160342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d159762 q = 1) : d160341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16470 q = 1) (hb : d159762 q = 1) : d160342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16470, d160342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16470, d160342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40270 (p : Pattern) (ha : d16476 p = 1) (hb : d159762 p = 1) : d178469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d159762 q = 1) : d178464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d178464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40268 q ha hb
    | true =>
      simp only [d16471, d178464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40269 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d159762 q = 1) : d178465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d178465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d178465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d159762 q = 1) : d178466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d178466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d178466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d159762 q = 1) : d178467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d178467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d178467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d159762 q = 1) : d178468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d178468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d178468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16476 q = 1) (hb : d159762 q = 1) : d178469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16476, d178469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16476, d178469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40271 (p : Pattern) (ha : d16479 p = 1) (hb : d159762 p = 1) : d178472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40266 q ha hb
    | true =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d159762 q = 1) : d178461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d159762 q = 1) : d178462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16479 q = 1) (hb : d159762 q = 1) : d178472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16479, d178472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16479, d178472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40272 (p : Pattern) (ha : d16480 p = 1) (hb : d159762 p = 1) : d160352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d159762 q = 1) : d160341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16480 q = 1) (hb : d159762 q = 1) : d160352 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16480, d160352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16480, d160352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40273 (p : Pattern) (ha : d16486 p = 1) (hb : d159762 p = 1) : d178478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d159762 q = 1) : d178464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d178464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40268 q ha hb
    | true =>
      simp only [d16471, d178464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40269 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d159762 q = 1) : d178465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d178465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d178465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d159762 q = 1) : d178466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d178466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d178466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d159762 q = 1) : d178467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d178467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d178467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d159762 q = 1) : d178468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d178468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d178468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16481 q = 1) (hb : d159762 q = 1) : d178473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d178473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40271 q ha hb
    | true =>
      simp only [d16481, d178473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40272 q ha hb
  have h7 (q : Pattern) (ha : d16482 q = 1) (hb : d159762 q = 1) : d178474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d178474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d178474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16483 q = 1) (hb : d159762 q = 1) : d178475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d178475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16483, d178475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16484 q = 1) (hb : d159762 q = 1) : d178476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d178476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d178476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16485 q = 1) (hb : d159762 q = 1) : d178477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d178477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d178477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16486 q = 1) (hb : d159762 q = 1) : d178478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16486, d178478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16486, d178478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40274 (p : Pattern) (ha : d16527 p = 1) (hb : d159762 p = 1) : d178457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d159762 q = 1) : d178452 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40264 q ha hb
    | true =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d159762 q = 1) : d178453 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d159762 q = 1) : d178454 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
    | true =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40262 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d159762 q = 1) : d178455 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16525 q = 1) (hb : d159762 q = 1) : d160326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16525, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16526 q = 1) (hb : d159762 q = 1) : d178456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d178456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16526, d178456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16527 q = 1) (hb : d159762 q = 1) : d178457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16527, d178457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16527, d178457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40275 (p : Pattern) (ha : d16537 p = 1) (hb : d159762 p = 1) : d178463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40274 q ha hb
    | true =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d159762 q = 1) : d178461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d159762 q = 1) : d178462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16537 q = 1) (hb : d159762 q = 1) : d178463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16537, d178463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16537, d178463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40276 (p : Pattern) (ha : d16628 p = 1) (hb : d159762 p = 1) : d178545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16618 q = 1) (hb : d159762 q = 1) : d178464 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16618, d178464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40275 q ha hb
    | true =>
      simp only [d16618, d178464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40269 q ha hb
  have h2 (q : Pattern) (ha : d16619 q = 1) (hb : d159762 q = 1) : d178465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16619, d178465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16619, d178465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16620 q = 1) (hb : d159762 q = 1) : d178466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16620, d178466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16620, d178466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16621 q = 1) (hb : d159762 q = 1) : d178467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16621, d178467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16621, d178467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16622 q = 1) (hb : d159762 q = 1) : d178468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16622, d178468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16622, d178468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16623 q = 1) (hb : d159762 q = 1) : d160432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40269 q ha hb
    | true =>
      simp only [d16623, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16624 q = 1) (hb : d159762 q = 1) : d160433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16625 q = 1) (hb : d159762 q = 1) : d160434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16625, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16626 q = 1) (hb : d159762 q = 1) : d160435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16627 q = 1) (hb : d159762 q = 1) : d160436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16628 q = 1) (hb : d159762 q = 1) : d178545 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16628, d178545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16628, d178545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40277 (p : Pattern) (ha : d16634 p = 1) (hb : d159762 p = 1) : d160443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16623 q = 1) (hb : d159762 q = 1) : d160432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40269 q ha hb
    | true =>
      simp only [d16623, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16624 q = 1) (hb : d159762 q = 1) : d160433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16625 q = 1) (hb : d159762 q = 1) : d160434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16625, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16626 q = 1) (hb : d159762 q = 1) : d160435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16627 q = 1) (hb : d159762 q = 1) : d160436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16629 q = 1) (hb : d159762 q = 1) : d160438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40272 q ha hb
    | true =>
      simp only [d16629, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16630 q = 1) (hb : d159762 q = 1) : d160439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16631 q = 1) (hb : d159762 q = 1) : d160440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16631, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16632 q = 1) (hb : d159762 q = 1) : d160441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16633 q = 1) (hb : d159762 q = 1) : d160442 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16634 q = 1) (hb : d159762 q = 1) : d160443 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16634, d160443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16634, d160443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40278 (p : Pattern) (ha : d16643 p = 1) (hb : d159762 p = 1) : d160452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16629 q = 1) (hb : d159762 q = 1) : d160438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40272 q ha hb
    | true =>
      simp only [d16629, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16630 q = 1) (hb : d159762 q = 1) : d160439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16631 q = 1) (hb : d159762 q = 1) : d160440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16631, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16632 q = 1) (hb : d159762 q = 1) : d160441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16633 q = 1) (hb : d159762 q = 1) : d160442 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16643 q = 1) (hb : d159762 q = 1) : d160452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16643, d160452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16643, d160452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40279 (p : Pattern) (ha : d15042 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1394 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1400 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1400, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15042 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15042, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40280 (p : Pattern) (ha : d16672 p = 1) (hb : d159762 p = 1) : d160472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1394 q = 1) (hb : d100904 q = 1) : d1394 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1395 q = 1) (hb : d159761 q = 1) : d160471 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d159761, d160471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1395, d159761, d160471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16672 q = 1) (hb : d159762 q = 1) : d160472 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d159762, d160472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16672, d159762, d160472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40281 (p : Pattern) (ha : d16698 p = 1) (hb : d159762 p = 1) : d160494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16693 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
    | true =>
      simp only [d16693, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40279 q ha hb
  have h2 (q : Pattern) (ha : d16694 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16695 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16696 q = 1) (hb : d159762 q = 1) : d160484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16696, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16697 q = 1) (hb : d159762 q = 1) : d160493 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d160493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16697, d160493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16698 q = 1) (hb : d159762 q = 1) : d160494 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16698, d160494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16698, d160494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40282 (p : Pattern) (ha : d16765 p = 1) (hb : d159762 p = 1) : d160517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16699 q = 1) (hb : d159762 q = 1) : d160495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40281 q ha hb
    | true =>
      simp only [d16699, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16700 q = 1) (hb : d159762 q = 1) : d160496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16762 q = 1) (hb : d159762 q = 1) : d160514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16762, d160514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16762, d160514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16763 q = 1) (hb : d159762 q = 1) : d160515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16763, d160515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16763, d160515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16764 q = 1) (hb : d159762 q = 1) : d160516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16764, d160516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16764, d160516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16765 q = 1) (hb : d159762 q = 1) : d160517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16765, d160517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16765, d160517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40283 (p : Pattern) (ha : d16771 p = 1) (hb : d159762 p = 1) : d160523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16766 q = 1) (hb : d159762 q = 1) : d160518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16766, d160518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40282 q ha hb
    | true =>
      simp only [d16766, d160518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16767 q = 1) (hb : d159762 q = 1) : d160519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16767, d160519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16767, d160519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16768 q = 1) (hb : d159762 q = 1) : d160520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16768, d160520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16768, d160520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16769 q = 1) (hb : d159762 q = 1) : d160521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16769, d160521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16769, d160521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16770 q = 1) (hb : d159762 q = 1) : d160522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16770, d160522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16770, d160522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16771 q = 1) (hb : d159762 q = 1) : d160523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16771, d160523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16771, d160523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40284 (p : Pattern) (ha : d16491 p = 1) (hb : d159762 p = 1) : d178483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40266 q ha hb
    | true =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d159762 q = 1) : d178461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d159762 q = 1) : d178482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d178482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d178482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16491 q = 1) (hb : d159762 q = 1) : d178483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16491, d178483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16491, d178483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40285 (p : Pattern) (ha : d16493 p = 1) (hb : d159762 p = 1) : d160365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d159762 q = 1) : d160364 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16493 q = 1) (hb : d159762 q = 1) : d160365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16493, d160365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16493, d160365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40286 (p : Pattern) (ha : d16500 p = 1) (hb : d159762 p = 1) : d178490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40266 q ha hb
    | true =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d159762 q = 1) : d178488 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d178488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d178488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d159762 q = 1) : d178489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d178489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d178489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16500 q = 1) (hb : d159762 q = 1) : d178490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16500, d178490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16500, d178490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40287 (p : Pattern) (ha : d16503 p = 1) (hb : d159762 p = 1) : d160375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d159762 q = 1) : d160373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d159762 q = 1) : d160374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16503 q = 1) (hb : d159762 q = 1) : d160375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16503, d160375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16503, d160375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40288 (p : Pattern) (ha : d16511 p = 1) (hb : d159762 p = 1) : d178495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16508 q = 1) (hb : d100904 q = 1) : d16508 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16509 q = 1) (hb : d159761 q = 1) : d178494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d159761, d178494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16509, d159761, d178494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16511 q = 1) (hb : d159762 q = 1) : d178495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d159762, d178495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16511, d159762, d178495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40289 (p : Pattern) (ha : d16516 p = 1) (hb : d159762 p = 1) : d178500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13023 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14764 q = 1) (hb : d100904 q = 1) : d14764 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16515 q = 1) (hb : d159761 q = 1) : d178499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d159761, d178499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16515, d159761, d178499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16516 q = 1) (hb : d159762 q = 1) : d178500 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d159762, d178500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16516, d159762, d178500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40290 (p : Pattern) (ha : d16522 p = 1) (hb : d159762 p = 1) : d178506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d159762 q = 1) : d178496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d178496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40288 q ha hb
    | true =>
      simp only [d16512, d178496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40264 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d159762 q = 1) : d178497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d178497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d178497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d159762 q = 1) : d178498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d178498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d178498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d159762 q = 1) : d178501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d178501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40264 q ha hb
    | true =>
      simp only [d16517, d178501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40289 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d159762 q = 1) : d178502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d178502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d178502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d159762 q = 1) : d178503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d178503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d178503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d159762 q = 1) : d178504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d178504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d178504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d159762 q = 1) : d178452 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40264 q ha hb
    | true =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d159762 q = 1) : d178453 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d159762 q = 1) : d178454 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16447 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
    | true =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40262 q ha hb
  have h12 (q : Pattern) (ha : d16448 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16449 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16450 q = 1) (hb : d159762 q = 1) : d178455 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16521 q = 1) (hb : d159762 q = 1) : d178505 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d178505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d178505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16522 q = 1) (hb : d159762 q = 1) : d178506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16522, d178506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16522, d178506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40291 (p : Pattern) (ha : d16533 p = 1) (hb : d159762 p = 1) : d178512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d159762 q = 1) : d178507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d178507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40290 q ha hb
    | true =>
      simp only [d16523, d178507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d159762 q = 1) : d178508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d178508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d178508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40274 q ha hb
    | true =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d159762 q = 1) : d178509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d178509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d178509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d159762 q = 1) : d178510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d178510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d178510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d159762 q = 1) : d178511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d178511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d178511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16533 q = 1) (hb : d159762 q = 1) : d178512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16533, d178512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16533, d178512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40292 (p : Pattern) (ha : d16579 p = 1) (hb : d159762 p = 1) : d178457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d159762 q = 1) : d178452 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40264 q ha hb
    | true =>
      simp only [d16444, d178452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d159762 q = 1) : d178453 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d178453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d159762 q = 1) : d178454 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d178454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
    | true =>
      simp only [d16447, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40262 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d159762 q = 1) : d178455 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d178455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16574 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40265 q ha hb
    | true =>
      simp only [d16574, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31547 q ha hb
  have h9 (q : Pattern) (ha : d16575 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16576 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16577 q = 1) (hb : d159762 q = 1) : d160326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16577, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16578 q = 1) (hb : d159762 q = 1) : d178456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d178456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16578, d178456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16579 q = 1) (hb : d159762 q = 1) : d178457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16579, d178457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16579, d178457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40293 (p : Pattern) (ha : d16585 p = 1) (hb : d159762 p = 1) : d178518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40292 q ha hb
    | true =>
      simp only [d16580, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d159762 q = 1) : d178515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d178515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d178515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d159762 q = 1) : d178516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d178516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d178516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d159762 q = 1) : d178517 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d178517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d178517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16585 q = 1) (hb : d159762 q = 1) : d178518 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16585, d178518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16585, d178518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40294 (p : Pattern) (ha : d128315 p = 1) (hb : d159762 p = 1) : d178524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d159762 q = 1) : d178484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d178484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40284 q ha hb
    | true =>
      simp only [d16494, d178484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40285 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d159762 q = 1) : d178485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d178485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d178485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d159762 q = 1) : d178486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d178486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d178486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d159762 q = 1) : d178487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d178487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d178487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d159762 q = 1) : d178491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d178491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40286 q ha hb
    | true =>
      simp only [d16504, d178491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40287 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d159762 q = 1) : d178492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d178492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d178492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d159762 q = 1) : d178493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d178493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d178493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d159762 q = 1) : d178513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d178513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40291 q ha hb
    | true =>
      simp only [d16538, d178513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40275 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d159762 q = 1) : d178514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d178514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d178514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d159762 q = 1) : d178519 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d178519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40293 q ha hb
    | true =>
      simp only [d16586, d178519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d159762 q = 1) : d178520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d178520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d178520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d159762 q = 1) : d178521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d178521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d178521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d159762 q = 1) : d178522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d178522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d178522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d159762 q = 1) : d178523 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d178523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d178523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128315 q = 1) (hb : d159762 q = 1) : d178524 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128315, d178524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128315, d178524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40295 (p : Pattern) (ha : d16592 p = 1) (hb : d159762 p = 1) : d178525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40266 q ha hb
    | true =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d159762 q = 1) : d178461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d159762 q = 1) : d178482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d178482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d178482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16592 q = 1) (hb : d159762 q = 1) : d178525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16592, d178525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16592, d178525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40296 (p : Pattern) (ha : d16593 p = 1) (hb : d159762 p = 1) : d160411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d159762 q = 1) : d160364 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16593 q = 1) (hb : d159762 q = 1) : d160411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16593, d160411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16593, d160411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40297 (p : Pattern) (ha : d16598 p = 1) (hb : d159762 p = 1) : d178530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40266 q ha hb
    | true =>
      simp only [d16457, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d159762 q = 1) : d178488 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d178488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d178488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d159762 q = 1) : d178489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d178489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d178489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16598 q = 1) (hb : d159762 q = 1) : d178530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16598, d178530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16598, d178530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40298 (p : Pattern) (ha : d16599 p = 1) (hb : d159762 p = 1) : d160417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d159762 q = 1) : d160373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d159762 q = 1) : d160374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16599 q = 1) (hb : d159762 q = 1) : d160417 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16599, d160417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16599, d160417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40299 (p : Pattern) (ha : d16603 p = 1) (hb : d159762 p = 1) : d178534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d159762 q = 1) : d178507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d178507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40290 q ha hb
    | true =>
      simp only [d16523, d178507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d159762 q = 1) : d178508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d178508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d178508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40274 q ha hb
    | true =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d159762 q = 1) : d178509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d178509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d178509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d159762 q = 1) : d178510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d178510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d178510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d159762 q = 1) : d178511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d178511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d178511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16603 q = 1) (hb : d159762 q = 1) : d178534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16603, d178534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16603, d178534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40300 (p : Pattern) (ha : d16604 p = 1) (hb : d159762 p = 1) : d178472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40274 q ha hb
    | true =>
      simp only [d16528, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40267 q ha hb
    | true =>
      simp only [d16461, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d159762 q = 1) : d178460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d178460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d159762 q = 1) : d178461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d178461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d159762 q = 1) : d178462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d178462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16604 q = 1) (hb : d159762 q = 1) : d178472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16604, d178472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16604, d178472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40301 (p : Pattern) (ha : d16610 p = 1) (hb : d159762 p = 1) : d178537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d159762 q = 1) : d178458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40292 q ha hb
    | true =>
      simp only [d16580, d178458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d159762 q = 1) : d178459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d178459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d159762 q = 1) : d178515 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d178515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d178515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d159762 q = 1) : d178516 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d178516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d178516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d159762 q = 1) : d178517 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d178517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d178517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16610 q = 1) (hb : d159762 q = 1) : d178537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16610, d178537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16610, d178537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40302 (p : Pattern) (ha : d128320 p = 1) (hb : d159762 p = 1) : d178543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d159762 q = 1) : d178484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d178484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40284 q ha hb
    | true =>
      simp only [d16494, d178484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40285 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d159762 q = 1) : d178485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d178485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d178485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d159762 q = 1) : d178486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d178486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d178486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d159762 q = 1) : d178487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d178487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d178487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d159762 q = 1) : d178491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d178491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40286 q ha hb
    | true =>
      simp only [d16504, d178491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40287 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d159762 q = 1) : d178492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d178492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d178492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d159762 q = 1) : d178493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d178493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d178493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d159762 q = 1) : d178513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d178513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40291 q ha hb
    | true =>
      simp only [d16538, d178513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40275 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d159762 q = 1) : d178514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d178514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d178514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d159762 q = 1) : d178519 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d178519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40293 q ha hb
    | true =>
      simp only [d16586, d178519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d159762 q = 1) : d178520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d178520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d178520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d159762 q = 1) : d178521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d178521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d178521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d159762 q = 1) : d178522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d178522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d178522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d159762 q = 1) : d178523 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d178523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d178523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16594 q = 1) (hb : d159762 q = 1) : d178526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16594, d178526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40295 q ha hb
    | true =>
      simp only [d16594, d178526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40296 q ha hb
  have h16 (q : Pattern) (ha : d16595 q = 1) (hb : d159762 q = 1) : d178527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16595, d178527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16595, d178527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16596 q = 1) (hb : d159762 q = 1) : d178528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16596, d178528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16596, d178528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16597 q = 1) (hb : d159762 q = 1) : d178529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16597, d178529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16597, d178529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16600 q = 1) (hb : d159762 q = 1) : d178531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16600, d178531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40297 q ha hb
    | true =>
      simp only [d16600, d178531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40298 q ha hb
  have h20 (q : Pattern) (ha : d16601 q = 1) (hb : d159762 q = 1) : d178532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16601, d178532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16601, d178532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16602 q = 1) (hb : d159762 q = 1) : d178533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16602, d178533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16602, d178533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16605 q = 1) (hb : d159762 q = 1) : d178535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d178535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40299 q ha hb
    | true =>
      simp only [d16605, d178535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40300 q ha hb
  have h23 (q : Pattern) (ha : d128316 q = 1) (hb : d159762 q = 1) : d178536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d178536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128316, d178536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16611 q = 1) (hb : d159762 q = 1) : d178538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d178538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40301 q ha hb
    | true =>
      simp only [d16611, d178538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16612 q = 1) (hb : d159762 q = 1) : d178539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d178539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16612, d178539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128317 q = 1) (hb : d159762 q = 1) : d178540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d178540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128317, d178540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128318 q = 1) (hb : d159762 q = 1) : d178541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128318, d178541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128318, d178541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128319 q = 1) (hb : d159762 q = 1) : d178542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128319, d178542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128319, d178542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128320 q = 1) (hb : d159762 q = 1) : d178543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128320, d178543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128320, d178543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro40303 (p : Pattern) (ha : d128327 p = 1) (hb : d159762 p = 1) : d178552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16605 q = 1) (hb : d159762 q = 1) : d178535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d178535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40299 q ha hb
    | true =>
      simp only [d16605, d178535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40300 q ha hb
  have h2 (q : Pattern) (ha : d128316 q = 1) (hb : d159762 q = 1) : d178536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d178536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128316, d178536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16611 q = 1) (hb : d159762 q = 1) : d178538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d178538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40301 q ha hb
    | true =>
      simp only [d16611, d178538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16612 q = 1) (hb : d159762 q = 1) : d178539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d178539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16612, d178539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128317 q = 1) (hb : d159762 q = 1) : d178540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d178540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128317, d178540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128325 q = 1) (hb : d159762 q = 1) : d178550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d178550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128325, d178550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128326 q = 1) (hb : d159762 q = 1) : d178551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d178551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128326, d178551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d159762 q = 1) : d178552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d178552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d178552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40304 (p : Pattern) (ha : d15024 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6353 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6354 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6354, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15023 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15024 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15024, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40305 (p : Pattern) (ha : d16655 p = 1) (hb : d159762 p = 1) : d178559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16652 q = 1) (hb : d100904 q = 1) : d16652 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16653 q = 1) (hb : d159761 q = 1) : d178558 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d159761, d178558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16653, d159761, d178558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16654 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16655 q = 1) (hb : d159762 q = 1) : d178559 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d159762, d178559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16655, d159762, d178559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40306 (p : Pattern) (ha : d16662 p = 1) (hb : d159762 p = 1) : d178561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1383 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16659 q = 1) (hb : d100904 q = 1) : d16659 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16660 q = 1) (hb : d159761 q = 1) : d178560 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d159761, d178560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16660, d159761, d178560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16661 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16662 q = 1) (hb : d159762 q = 1) : d178561 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d159762, d178561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16662, d159762, d178561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40307 (p : Pattern) (ha : d16667 p = 1) (hb : d159762 p = 1) : d178566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13163 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15007 q = 1) (hb : d100904 q = 1) : d15007 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16666 q = 1) (hb : d159761 q = 1) : d178565 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d159761, d178565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16666, d159761, d178565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16667 q = 1) (hb : d159762 q = 1) : d178566 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d159762, d178566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16667, d159762, d178566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40308 (p : Pattern) (ha : d16681 p = 1) (hb : d159762 p = 1) : d178576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d159762 q = 1) : d178562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d178562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40305 q ha hb
    | true =>
      simp only [d16663, d178562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40306 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d159762 q = 1) : d178563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d178563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d178563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d159762 q = 1) : d178564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d178564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d178564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d159762 q = 1) : d178567 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d178567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40306 q ha hb
    | true =>
      simp only [d16668, d178567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40307 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d159762 q = 1) : d178568 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d178568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d178568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d159762 q = 1) : d178569 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d178569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d178569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d159762 q = 1) : d178570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d178570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d178570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d159762 q = 1) : d178571 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40306 q ha hb
    | true =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d159762 q = 1) : d178572 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d159762 q = 1) : d178573 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16676 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
    | true =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40304 q ha hb
  have h12 (q : Pattern) (ha : d16677 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16678 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16679 q = 1) (hb : d159762 q = 1) : d178574 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16680 q = 1) (hb : d159762 q = 1) : d178575 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d178575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d178575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16681 q = 1) (hb : d159762 q = 1) : d178576 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16681, d178576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16681, d178576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40309 (p : Pattern) (ha : d16686 p = 1) (hb : d159762 p = 1) : d178580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d159762 q = 1) : d178571 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40306 q ha hb
    | true =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d159762 q = 1) : d178572 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d159762 q = 1) : d178573 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
    | true =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40304 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d159762 q = 1) : d178574 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16684 q = 1) (hb : d159762 q = 1) : d160484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16684, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16685 q = 1) (hb : d159762 q = 1) : d178579 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d178579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16685, d178579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16686 q = 1) (hb : d159762 q = 1) : d178580 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16686, d178580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16686, d178580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40310 (p : Pattern) (ha : d16692 p = 1) (hb : d159762 p = 1) : d178586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16682 q = 1) (hb : d159762 q = 1) : d178577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16682, d178577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40308 q ha hb
    | true =>
      simp only [d16682, d178577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16683 q = 1) (hb : d159762 q = 1) : d178578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16683, d178578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16683, d178578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16687 q = 1) (hb : d159762 q = 1) : d178581 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40309 q ha hb
    | true =>
      simp only [d16687, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16688 q = 1) (hb : d159762 q = 1) : d178582 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16689 q = 1) (hb : d159762 q = 1) : d178583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16689, d178583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16689, d178583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16690 q = 1) (hb : d159762 q = 1) : d178584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16690, d178584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16690, d178584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16691 q = 1) (hb : d159762 q = 1) : d178585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16691, d178585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16691, d178585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16692 q = 1) (hb : d159762 q = 1) : d178586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16692, d178586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16692, d178586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40311 (p : Pattern) (ha : d16704 p = 1) (hb : d159762 p = 1) : d178590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16687 q = 1) (hb : d159762 q = 1) : d178581 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40309 q ha hb
    | true =>
      simp only [d16687, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16688 q = 1) (hb : d159762 q = 1) : d178582 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d159762 q = 1) : d160495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40281 q ha hb
    | true =>
      simp only [d16699, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d159762 q = 1) : d160496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16701 q = 1) (hb : d159762 q = 1) : d178587 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16701, d178587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16701, d178587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16702 q = 1) (hb : d159762 q = 1) : d178588 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16702, d178588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16702, d178588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16703 q = 1) (hb : d159762 q = 1) : d178589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16703, d178589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16703, d178589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16704 q = 1) (hb : d159762 q = 1) : d178590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16704, d178590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16704, d178590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40312 (p : Pattern) (ha : d16748 p = 1) (hb : d159762 p = 1) : d178580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d159762 q = 1) : d178571 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40306 q ha hb
    | true =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d159762 q = 1) : d178572 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d159762 q = 1) : d178573 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
    | true =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40304 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d159762 q = 1) : d178574 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16743 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
    | true =>
      simp only [d16743, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31562 q ha hb
  have h9 (q : Pattern) (ha : d16744 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16745 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16746 q = 1) (hb : d159762 q = 1) : d160484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16746, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16747 q = 1) (hb : d159762 q = 1) : d178579 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d178579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d178579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16748 q = 1) (hb : d159762 q = 1) : d178580 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16748, d178580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16748, d178580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40313 (p : Pattern) (ha : d16754 p = 1) (hb : d159762 p = 1) : d178596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16749 q = 1) (hb : d159762 q = 1) : d178581 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16749, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40312 q ha hb
    | true =>
      simp only [d16749, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16750 q = 1) (hb : d159762 q = 1) : d178582 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16750, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16750, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16751 q = 1) (hb : d159762 q = 1) : d178593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16751, d178593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16751, d178593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16752 q = 1) (hb : d159762 q = 1) : d178594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16752, d178594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16752, d178594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16753 q = 1) (hb : d159762 q = 1) : d178595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16753, d178595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16753, d178595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16754 q = 1) (hb : d159762 q = 1) : d178596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16754, d178596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16754, d178596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40314 (p : Pattern) (ha : d128337 p = 1) (hb : d159762 p = 1) : d178602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16705 q = 1) (hb : d159762 q = 1) : d178591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16705, d178591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40310 q ha hb
    | true =>
      simp only [d16705, d178591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40311 q ha hb
  have h2 (q : Pattern) (ha : d128333 q = 1) (hb : d159762 q = 1) : d178592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d178592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128333, d178592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16755 q = 1) (hb : d159762 q = 1) : d178597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16755, d178597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40313 q ha hb
    | true =>
      simp only [d16755, d178597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16756 q = 1) (hb : d159762 q = 1) : d178598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16756, d178598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16756, d178598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d159762 q = 1) : d178599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d178599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128334, d178599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d159762 q = 1) : d178600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d178600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d178600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d159762 q = 1) : d178601 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d178601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d178601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d159762 q = 1) : d178602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d178602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d178602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40315 (p : Pattern) (ha : d128343 p = 1) (hb : d159762 p = 1) : d178608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16477 q = 1) (hb : d159762 q = 1) : d178470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16477, d178470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16477, d178470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40270 q ha hb
  have h2 (q : Pattern) (ha : d16478 q = 1) (hb : d159762 q = 1) : d178471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16478, d178471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16478, d178471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16487 q = 1) (hb : d159762 q = 1) : d178479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d178479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40270 q ha hb
    | true =>
      simp only [d16487, d178479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40273 q ha hb
  have h4 (q : Pattern) (ha : d16488 q = 1) (hb : d159762 q = 1) : d178480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d178480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16488, d178480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16489 q = 1) (hb : d159762 q = 1) : d178481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16489, d178481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16489, d178481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128321 q = 1) (hb : d159762 q = 1) : d178544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128321, d178544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40294 q ha hb
    | true =>
      simp only [d128321, d178544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40302 q ha hb
  have h7 (q : Pattern) (ha : d16635 q = 1) (hb : d159762 q = 1) : d178546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16635, d178546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40276 q ha hb
    | true =>
      simp only [d16635, d178546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40277 q ha hb
  have h8 (q : Pattern) (ha : d128322 q = 1) (hb : d159762 q = 1) : d178547 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128322, d178547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128322, d178547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128323 q = 1) (hb : d159762 q = 1) : d178548 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d178548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128323, d178548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128324 q = 1) (hb : d159762 q = 1) : d178549 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d178549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128324, d178549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128328 q = 1) (hb : d159762 q = 1) : d178553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d178553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128328, d178553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40303 q ha hb
  have h12 (q : Pattern) (ha : d16644 q = 1) (hb : d159762 q = 1) : d160453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16644, d160453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16644, d160453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40278 q ha hb
  have h13 (q : Pattern) (ha : d128329 q = 1) (hb : d159762 q = 1) : d178554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d178554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128329, d178554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128330 q = 1) (hb : d159762 q = 1) : d178555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d178555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128330, d178555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128331 q = 1) (hb : d159762 q = 1) : d178556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d178556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128331, d178556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128332 q = 1) (hb : d159762 q = 1) : d178557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d178557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128332, d178557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128338 q = 1) (hb : d159762 q = 1) : d178603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d178603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128338, d178603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40314 q ha hb
  have h18 (q : Pattern) (ha : d16772 q = 1) (hb : d159762 q = 1) : d160524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16772, d160524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16772, d160524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40283 q ha hb
  have h19 (q : Pattern) (ha : d128339 q = 1) (hb : d159762 q = 1) : d178604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d178604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128339, d178604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128340 q = 1) (hb : d159762 q = 1) : d178605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d178605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128340, d178605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128341 q = 1) (hb : d159762 q = 1) : d178606 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d178606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128341, d178606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128342 q = 1) (hb : d159762 q = 1) : d178607 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d178607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128342, d178607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128343 q = 1) (hb : d159762 q = 1) : d178608 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d178608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128343, d178608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40316 (p : Pattern) (ha : d128349 p = 1) (hb : d159762 p = 1) : d178614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d159762 q = 1) : d178609 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d178609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d178609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40315 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d159762 q = 1) : d178610 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d178610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d178610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d159762 q = 1) : d178611 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d178611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d178611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d159762 q = 1) : d178612 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d178612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d178612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d159762 q = 1) : d178613 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d178613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d178613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d159762 q = 1) : d178614 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d178614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d178614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40317 (p : Pattern) (ha : d15166 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5137 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5138 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5138, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15166 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15166, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40318 (p : Pattern) (ha : d15171 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1585 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1588 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1588, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15165 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15171 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15171, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40319 (p : Pattern) (ha : d16791 p = 1) (hb : d159762 p = 1) : d178619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16788 q = 1) (hb : d100904 q = 1) : d16788 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16789 q = 1) (hb : d159761 q = 1) : d178618 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d159761, d178618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16789, d159761, d178618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16790 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16791 q = 1) (hb : d159762 q = 1) : d178619 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d159762, d178619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16791, d159762, d178619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40320 (p : Pattern) (ha : d16795 p = 1) (hb : d159762 p = 1) : d178621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16793 q = 1) (hb : d100904 q = 1) : d16793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16794 q = 1) (hb : d159761 q = 1) : d178620 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d159761, d178620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16794, d159761, d178620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15158 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16795 q = 1) (hb : d159762 q = 1) : d178621 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d159762, d178621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16795, d159762, d178621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40321 (p : Pattern) (ha : d16808 p = 1) (hb : d159762 p = 1) : d178631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d159762 q = 1) : d178622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40319 q ha hb
    | true =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d159762 q = 1) : d178623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d159762 q = 1) : d178624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d159762 q = 1) : d178625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
    | true =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40317 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d159762 q = 1) : d178626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d159762 q = 1) : d178627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d159762 q = 1) : d178628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16803 q = 1) (hb : d159762 q = 1) : d178625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
    | true =>
      simp only [d16803, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40318 q ha hb
  have h9 (q : Pattern) (ha : d16804 q = 1) (hb : d159762 q = 1) : d178626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16805 q = 1) (hb : d159762 q = 1) : d178627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16806 q = 1) (hb : d159762 q = 1) : d178629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16806, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16807 q = 1) (hb : d159762 q = 1) : d178630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d178630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16807, d178630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16808 q = 1) (hb : d159762 q = 1) : d178631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d178631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16808, d178631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40322 (p : Pattern) (ha : d16812 p = 1) (hb : d159762 p = 1) : d178635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d159762 q = 1) : d178625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
    | true =>
      simp only [d16803, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40318 q ha hb
  have h2 (q : Pattern) (ha : d16804 q = 1) (hb : d159762 q = 1) : d178626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16805 q = 1) (hb : d159762 q = 1) : d178627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16806 q = 1) (hb : d159762 q = 1) : d178629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16806, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16811 q = 1) (hb : d159762 q = 1) : d178634 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d178634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16811, d178634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16812 q = 1) (hb : d159762 q = 1) : d178635 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d178635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16812, d178635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40323 (p : Pattern) (ha : d16818 p = 1) (hb : d159762 p = 1) : d178641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40321 q ha hb
    | true =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d159762 q = 1) : d178639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d159762 q = 1) : d178640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16818 q = 1) (hb : d159762 q = 1) : d178641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16818, d178641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16818, d178641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40324 (p : Pattern) (ha : d16822 p = 1) (hb : d159762 p = 1) : d178645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d159762 q = 1) : d178642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d159762 q = 1) : d178643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d159762 q = 1) : d178644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d178644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d178644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16822 q = 1) (hb : d159762 q = 1) : d178645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16822, d178645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16822, d178645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40325 (p : Pattern) (ha : d16828 p = 1) (hb : d159762 p = 1) : d178651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d159762 q = 1) : d178646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d178646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40323 q ha hb
    | true =>
      simp only [d16823, d178646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40324 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d159762 q = 1) : d178647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d178647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d178647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d159762 q = 1) : d178648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d178648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d178648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d159762 q = 1) : d178649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d178649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d178649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d159762 q = 1) : d178650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d178650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d178650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16828 q = 1) (hb : d159762 q = 1) : d178651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16828, d178651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16828, d178651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40326 (p : Pattern) (ha : d16831 p = 1) (hb : d159762 p = 1) : d178654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40321 q ha hb
    | true =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d159762 q = 1) : d178639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d159762 q = 1) : d178640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16831 q = 1) (hb : d159762 q = 1) : d178654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16831, d178654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16831, d178654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40327 (p : Pattern) (ha : d16832 p = 1) (hb : d159762 p = 1) : d178655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d159762 q = 1) : d178642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d159762 q = 1) : d178643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d159762 q = 1) : d178644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d178644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d178644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16832 q = 1) (hb : d159762 q = 1) : d178655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16832, d178655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16832, d178655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40328 (p : Pattern) (ha : d16838 p = 1) (hb : d159762 p = 1) : d178661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d159762 q = 1) : d178646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d178646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40323 q ha hb
    | true =>
      simp only [d16823, d178646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40324 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d159762 q = 1) : d178647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d178647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d178647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d159762 q = 1) : d178648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d178648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d178648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d159762 q = 1) : d178649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d178649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d178649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d159762 q = 1) : d178650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d178650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d178650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16833 q = 1) (hb : d159762 q = 1) : d178656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d178656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40326 q ha hb
    | true =>
      simp only [d16833, d178656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40327 q ha hb
  have h7 (q : Pattern) (ha : d16834 q = 1) (hb : d159762 q = 1) : d178657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d178657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d178657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16835 q = 1) (hb : d159762 q = 1) : d178658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d178658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16835, d178658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16836 q = 1) (hb : d159762 q = 1) : d178659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d178659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d178659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16837 q = 1) (hb : d159762 q = 1) : d178660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d178660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d178660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16838 q = 1) (hb : d159762 q = 1) : d178661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16838, d178661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16838, d178661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40329 (p : Pattern) (ha : d16879 p = 1) (hb : d159762 p = 1) : d178631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d159762 q = 1) : d178622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40319 q ha hb
    | true =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d159762 q = 1) : d178623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d159762 q = 1) : d178624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d159762 q = 1) : d178625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
    | true =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40317 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d159762 q = 1) : d178626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d159762 q = 1) : d178627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d159762 q = 1) : d178628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16877 q = 1) (hb : d159762 q = 1) : d178629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16877, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16878 q = 1) (hb : d159762 q = 1) : d178630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d178630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16878, d178630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16879 q = 1) (hb : d159762 q = 1) : d178631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16879, d178631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16879, d178631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40330 (p : Pattern) (ha : d16889 p = 1) (hb : d159762 p = 1) : d178641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40329 q ha hb
    | true =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d159762 q = 1) : d178639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d159762 q = 1) : d178640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16889 q = 1) (hb : d159762 q = 1) : d178641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16889, d178641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16889, d178641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40331 (p : Pattern) (ha : d16983 p = 1) (hb : d159762 p = 1) : d178740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16973 q = 1) (hb : d159762 q = 1) : d178646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16973, d178646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40330 q ha hb
    | true =>
      simp only [d16973, d178646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40324 q ha hb
  have h2 (q : Pattern) (ha : d16974 q = 1) (hb : d159762 q = 1) : d178647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16974, d178647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16974, d178647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16975 q = 1) (hb : d159762 q = 1) : d178648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16975, d178648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16975, d178648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16976 q = 1) (hb : d159762 q = 1) : d178649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16976, d178649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16976, d178649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16977 q = 1) (hb : d159762 q = 1) : d178650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16977, d178650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16977, d178650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16978 q = 1) (hb : d159762 q = 1) : d178735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d178735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40324 q ha hb
    | true =>
      simp only [d16978, d178735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16979 q = 1) (hb : d159762 q = 1) : d178736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d178736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d178736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16980 q = 1) (hb : d159762 q = 1) : d178737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d178737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16980, d178737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16981 q = 1) (hb : d159762 q = 1) : d178738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d178738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d178738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16982 q = 1) (hb : d159762 q = 1) : d178739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d178739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d178739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16983 q = 1) (hb : d159762 q = 1) : d178740 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16983, d178740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16983, d178740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40332 (p : Pattern) (ha : d16989 p = 1) (hb : d159762 p = 1) : d178746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16978 q = 1) (hb : d159762 q = 1) : d178735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d178735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40324 q ha hb
    | true =>
      simp only [d16978, d178735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16979 q = 1) (hb : d159762 q = 1) : d178736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d178736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d178736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16980 q = 1) (hb : d159762 q = 1) : d178737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d178737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16980, d178737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16981 q = 1) (hb : d159762 q = 1) : d178738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d178738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d178738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16982 q = 1) (hb : d159762 q = 1) : d178739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d178739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d178739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16984 q = 1) (hb : d159762 q = 1) : d178741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d178741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40327 q ha hb
    | true =>
      simp only [d16984, d178741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16985 q = 1) (hb : d159762 q = 1) : d178742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d178742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d178742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16986 q = 1) (hb : d159762 q = 1) : d178743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d178743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16986, d178743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16987 q = 1) (hb : d159762 q = 1) : d178744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d178744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d178744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16988 q = 1) (hb : d159762 q = 1) : d178745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d178745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d178745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16989 q = 1) (hb : d159762 q = 1) : d178746 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16989, d178746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16989, d178746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40333 (p : Pattern) (ha : d16998 p = 1) (hb : d159762 p = 1) : d178755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16984 q = 1) (hb : d159762 q = 1) : d178741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d178741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40327 q ha hb
    | true =>
      simp only [d16984, d178741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16985 q = 1) (hb : d159762 q = 1) : d178742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d178742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d178742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16986 q = 1) (hb : d159762 q = 1) : d178743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d178743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16986, d178743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16987 q = 1) (hb : d159762 q = 1) : d178744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d178744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d178744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16988 q = 1) (hb : d159762 q = 1) : d178745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d178745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d178745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16998 q = 1) (hb : d159762 q = 1) : d178755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16998, d178755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16998, d178755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40334 (p : Pattern) (ha : d15435 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1871 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1877 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1877, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15435 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15435, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40335 (p : Pattern) (ha : d17032 p = 1) (hb : d159762 p = 1) : d178775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1865 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17030 q = 1) (hb : d100904 q = 1) : d17030 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17031 q = 1) (hb : d159761 q = 1) : d178774 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d159761, d178774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17031, d159761, d178774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15401 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17032 q = 1) (hb : d159762 q = 1) : d178775 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d159762, d178775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17032, d159762, d178775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40336 (p : Pattern) (ha : d17058 p = 1) (hb : d159762 p = 1) : d178797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d159762 q = 1) : d178779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
    | true =>
      simp only [d17053, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40334 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d159762 q = 1) : d178780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d159762 q = 1) : d178781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d159762 q = 1) : d178787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d159762 q = 1) : d178796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d178796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d178796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17058 q = 1) (hb : d159762 q = 1) : d178797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17058, d178797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17058, d178797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40337 (p : Pattern) (ha : d17130 p = 1) (hb : d159762 p = 1) : d178820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17059 q = 1) (hb : d159762 q = 1) : d178798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d178798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40336 q ha hb
    | true =>
      simp only [d17059, d178798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17060 q = 1) (hb : d159762 q = 1) : d178799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d178799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d178799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17127 q = 1) (hb : d159762 q = 1) : d178817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17127, d178817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17127, d178817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17128 q = 1) (hb : d159762 q = 1) : d178818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17128, d178818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17128, d178818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17129 q = 1) (hb : d159762 q = 1) : d178819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17129, d178819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17129, d178819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17130 q = 1) (hb : d159762 q = 1) : d178820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17130, d178820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17130, d178820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40338 (p : Pattern) (ha : d17136 p = 1) (hb : d159762 p = 1) : d178826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17131 q = 1) (hb : d159762 q = 1) : d178821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17131, d178821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40337 q ha hb
    | true =>
      simp only [d17131, d178821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17132 q = 1) (hb : d159762 q = 1) : d178822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17132, d178822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17132, d178822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17133 q = 1) (hb : d159762 q = 1) : d178823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17133, d178823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17133, d178823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17134 q = 1) (hb : d159762 q = 1) : d178824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17134, d178824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17134, d178824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17135 q = 1) (hb : d159762 q = 1) : d178825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17135, d178825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17135, d178825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17136 q = 1) (hb : d159762 q = 1) : d178826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17136, d178826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17136, d178826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40339 (p : Pattern) (ha : d16843 p = 1) (hb : d159762 p = 1) : d178666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40321 q ha hb
    | true =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d159762 q = 1) : d178639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d159762 q = 1) : d178665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d178665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d178665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16843 q = 1) (hb : d159762 q = 1) : d178666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16843, d178666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16843, d178666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40340 (p : Pattern) (ha : d16845 p = 1) (hb : d159762 p = 1) : d178668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d159762 q = 1) : d178642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d159762 q = 1) : d178643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d159762 q = 1) : d178667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d178667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d178667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16845 q = 1) (hb : d159762 q = 1) : d178668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16845, d178668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16845, d178668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40341 (p : Pattern) (ha : d16852 p = 1) (hb : d159762 p = 1) : d178675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40321 q ha hb
    | true =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d159762 q = 1) : d178673 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d178673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d178673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d159762 q = 1) : d178674 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d178674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d178674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16852 q = 1) (hb : d159762 q = 1) : d178675 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16852, d178675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16852, d178675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40342 (p : Pattern) (ha : d16855 p = 1) (hb : d159762 p = 1) : d178678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d159762 q = 1) : d178642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d159762 q = 1) : d178676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d178676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d178676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d159762 q = 1) : d178677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d178677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d178677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16855 q = 1) (hb : d159762 q = 1) : d178678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16855, d178678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16855, d178678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40343 (p : Pattern) (ha : d16863 p = 1) (hb : d159762 p = 1) : d178683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1668 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16860 q = 1) (hb : d100904 q = 1) : d16860 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16861 q = 1) (hb : d159761 q = 1) : d178682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d159761, d178682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16861, d159761, d178682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16862 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16863 q = 1) (hb : d159762 q = 1) : d178683 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d159762, d178683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16863, d159762, d178683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40344 (p : Pattern) (ha : d16868 p = 1) (hb : d159762 p = 1) : d178688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13349 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15157 q = 1) (hb : d100904 q = 1) : d15157 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16867 q = 1) (hb : d159761 q = 1) : d178687 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d159761, d178687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16867, d159761, d178687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15158 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16868 q = 1) (hb : d159762 q = 1) : d178688 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d159762, d178688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16868, d159762, d178688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40345 (p : Pattern) (ha : d16874 p = 1) (hb : d159762 p = 1) : d178694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d159762 q = 1) : d178684 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d178684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40343 q ha hb
    | true =>
      simp only [d16864, d178684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40319 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d159762 q = 1) : d178685 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d178685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d178685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d159762 q = 1) : d178686 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d178686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d178686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d159762 q = 1) : d178689 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d178689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40319 q ha hb
    | true =>
      simp only [d16869, d178689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40344 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d159762 q = 1) : d178690 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d178690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d178690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d159762 q = 1) : d178691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d178691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d178691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d159762 q = 1) : d178692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d178692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d178692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d159762 q = 1) : d178622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40319 q ha hb
    | true =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d159762 q = 1) : d178623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d159762 q = 1) : d178624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16799 q = 1) (hb : d159762 q = 1) : d178625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
    | true =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40317 q ha hb
  have h12 (q : Pattern) (ha : d16800 q = 1) (hb : d159762 q = 1) : d178626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16801 q = 1) (hb : d159762 q = 1) : d178627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16802 q = 1) (hb : d159762 q = 1) : d178628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16873 q = 1) (hb : d159762 q = 1) : d178693 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d178693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d178693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16874 q = 1) (hb : d159762 q = 1) : d178694 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16874, d178694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16874, d178694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40346 (p : Pattern) (ha : d16885 p = 1) (hb : d159762 p = 1) : d178700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d159762 q = 1) : d178695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d178695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40345 q ha hb
    | true =>
      simp only [d16875, d178695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d159762 q = 1) : d178696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d178696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d178696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40329 q ha hb
    | true =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d159762 q = 1) : d178697 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d178697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d178697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d159762 q = 1) : d178698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d178698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d178698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d159762 q = 1) : d178699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d178699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d178699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16885 q = 1) (hb : d159762 q = 1) : d178700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16885, d178700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16885, d178700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40347 (p : Pattern) (ha : d16934 p = 1) (hb : d159762 p = 1) : d178631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d159762 q = 1) : d178622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40319 q ha hb
    | true =>
      simp only [d16796, d178622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d159762 q = 1) : d178623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d178623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d159762 q = 1) : d178624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d178624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d159762 q = 1) : d178625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
    | true =>
      simp only [d16799, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40317 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d159762 q = 1) : d178626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d159762 q = 1) : d178627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d159762 q = 1) : d178628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d178628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16929 q = 1) (hb : d159762 q = 1) : d178625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40320 q ha hb
    | true =>
      simp only [d16929, d178625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31601 q ha hb
  have h9 (q : Pattern) (ha : d16930 q = 1) (hb : d159762 q = 1) : d178626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16930, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16930, d178626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16931 q = 1) (hb : d159762 q = 1) : d178627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16931, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16931, d178627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16932 q = 1) (hb : d159762 q = 1) : d178629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16932, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16932, d178629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16933 q = 1) (hb : d159762 q = 1) : d178630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16933, d178630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16933, d178630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16934 q = 1) (hb : d159762 q = 1) : d178631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16934, d178631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16934, d178631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40348 (p : Pattern) (ha : d16940 p = 1) (hb : d159762 p = 1) : d178706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40347 q ha hb
    | true =>
      simp only [d16935, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d159762 q = 1) : d178703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d178703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d178703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d159762 q = 1) : d178704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d178704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d178704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d159762 q = 1) : d178705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d178705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d178705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16940 q = 1) (hb : d159762 q = 1) : d178706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16940, d178706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16940, d178706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40349 (p : Pattern) (ha : d128357 p = 1) (hb : d159762 p = 1) : d178712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d159762 q = 1) : d178669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d178669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40339 q ha hb
    | true =>
      simp only [d16846, d178669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40340 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d159762 q = 1) : d178670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d178670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d178670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d159762 q = 1) : d178671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d178671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d178671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d159762 q = 1) : d178672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d178672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d178672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d159762 q = 1) : d178679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d178679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40341 q ha hb
    | true =>
      simp only [d16856, d178679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40342 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d159762 q = 1) : d178680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d178680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d178680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d159762 q = 1) : d178681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d178681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d178681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d159762 q = 1) : d178701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d178701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40346 q ha hb
    | true =>
      simp only [d16890, d178701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40330 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d159762 q = 1) : d178702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d178702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d178702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d159762 q = 1) : d178707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d178707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40348 q ha hb
    | true =>
      simp only [d16941, d178707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d159762 q = 1) : d178708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d178708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d178708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d159762 q = 1) : d178709 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d178709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d178709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d159762 q = 1) : d178710 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d178710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d178710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d159762 q = 1) : d178711 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d178711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d178711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128357 q = 1) (hb : d159762 q = 1) : d178712 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128357, d178712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128357, d178712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40350 (p : Pattern) (ha : d16947 p = 1) (hb : d159762 p = 1) : d178713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40321 q ha hb
    | true =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d159762 q = 1) : d178639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d159762 q = 1) : d178665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d178665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d178665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16947 q = 1) (hb : d159762 q = 1) : d178713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16947, d178713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16947, d178713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40351 (p : Pattern) (ha : d16948 p = 1) (hb : d159762 p = 1) : d178714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d159762 q = 1) : d178642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d159762 q = 1) : d178643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d178643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d159762 q = 1) : d178667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d178667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d178667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16948 q = 1) (hb : d159762 q = 1) : d178714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16948, d178714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16948, d178714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40352 (p : Pattern) (ha : d16953 p = 1) (hb : d159762 p = 1) : d178719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40321 q ha hb
    | true =>
      simp only [d16809, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d159762 q = 1) : d178673 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d178673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d178673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d159762 q = 1) : d178674 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d178674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d178674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16953 q = 1) (hb : d159762 q = 1) : d178719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16953, d178719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16953, d178719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40353 (p : Pattern) (ha : d16954 p = 1) (hb : d159762 p = 1) : d178720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d159762 q = 1) : d178642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d178642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d159762 q = 1) : d178676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d178676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d178676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d159762 q = 1) : d178677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d178677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d178677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16954 q = 1) (hb : d159762 q = 1) : d178720 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16954, d178720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16954, d178720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40354 (p : Pattern) (ha : d16958 p = 1) (hb : d159762 p = 1) : d178724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d159762 q = 1) : d178695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d178695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40345 q ha hb
    | true =>
      simp only [d16875, d178695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d159762 q = 1) : d178696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d178696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d178696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40329 q ha hb
    | true =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d159762 q = 1) : d178697 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d178697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d178697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d159762 q = 1) : d178698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d178698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d178698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d159762 q = 1) : d178699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d178699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d178699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16958 q = 1) (hb : d159762 q = 1) : d178724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16958, d178724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16958, d178724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40355 (p : Pattern) (ha : d16959 p = 1) (hb : d159762 p = 1) : d178654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40329 q ha hb
    | true =>
      simp only [d16880, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d159762 q = 1) : d178636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40322 q ha hb
    | true =>
      simp only [d16813, d178636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d159762 q = 1) : d178637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d178637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d159762 q = 1) : d178638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d178638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d159762 q = 1) : d178639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d178639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d159762 q = 1) : d178640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d178640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16959 q = 1) (hb : d159762 q = 1) : d178654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16959, d178654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16959, d178654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40356 (p : Pattern) (ha : d16965 p = 1) (hb : d159762 p = 1) : d178727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d159762 q = 1) : d178632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40347 q ha hb
    | true =>
      simp only [d16935, d178632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d159762 q = 1) : d178633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d178633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d159762 q = 1) : d178703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d178703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d178703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d159762 q = 1) : d178704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d178704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d178704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d159762 q = 1) : d178705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d178705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d178705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16965 q = 1) (hb : d159762 q = 1) : d178727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16965, d178727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16965, d178727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40357 (p : Pattern) (ha : d128362 p = 1) (hb : d159762 p = 1) : d178733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d159762 q = 1) : d178669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d178669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40339 q ha hb
    | true =>
      simp only [d16846, d178669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40340 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d159762 q = 1) : d178670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d178670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d178670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d159762 q = 1) : d178671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d178671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d178671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d159762 q = 1) : d178672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d178672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d178672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d159762 q = 1) : d178679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d178679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40341 q ha hb
    | true =>
      simp only [d16856, d178679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40342 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d159762 q = 1) : d178680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d178680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d178680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d159762 q = 1) : d178681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d178681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d178681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d159762 q = 1) : d178701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d178701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40346 q ha hb
    | true =>
      simp only [d16890, d178701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40330 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d159762 q = 1) : d178702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d178702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d178702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d159762 q = 1) : d178707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d178707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40348 q ha hb
    | true =>
      simp only [d16941, d178707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d159762 q = 1) : d178708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d178708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d178708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d159762 q = 1) : d178709 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d178709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d178709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d159762 q = 1) : d178710 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d178710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d178710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d159762 q = 1) : d178711 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d178711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d178711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16949 q = 1) (hb : d159762 q = 1) : d178715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16949, d178715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40350 q ha hb
    | true =>
      simp only [d16949, d178715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40351 q ha hb
  have h16 (q : Pattern) (ha : d16950 q = 1) (hb : d159762 q = 1) : d178716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16950, d178716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16950, d178716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16951 q = 1) (hb : d159762 q = 1) : d178717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16951, d178717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16951, d178717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16952 q = 1) (hb : d159762 q = 1) : d178718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16952, d178718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16952, d178718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16955 q = 1) (hb : d159762 q = 1) : d178721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16955, d178721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40352 q ha hb
    | true =>
      simp only [d16955, d178721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40353 q ha hb
  have h20 (q : Pattern) (ha : d16956 q = 1) (hb : d159762 q = 1) : d178722 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16956, d178722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16956, d178722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16957 q = 1) (hb : d159762 q = 1) : d178723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16957, d178723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16957, d178723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16960 q = 1) (hb : d159762 q = 1) : d178725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d178725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40354 q ha hb
    | true =>
      simp only [d16960, d178725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40355 q ha hb
  have h23 (q : Pattern) (ha : d128358 q = 1) (hb : d159762 q = 1) : d178726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d178726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128358, d178726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16966 q = 1) (hb : d159762 q = 1) : d178728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d178728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40356 q ha hb
    | true =>
      simp only [d16966, d178728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16967 q = 1) (hb : d159762 q = 1) : d178729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d178729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16967, d178729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128359 q = 1) (hb : d159762 q = 1) : d178730 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d178730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128359, d178730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128360 q = 1) (hb : d159762 q = 1) : d178731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128360, d178731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128360, d178731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128361 q = 1) (hb : d159762 q = 1) : d178732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128361, d178732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128361, d178732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128362 q = 1) (hb : d159762 q = 1) : d178733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128362, d178733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128362, d178733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro40358 (p : Pattern) (ha : d128369 p = 1) (hb : d159762 p = 1) : d178753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16960 q = 1) (hb : d159762 q = 1) : d178725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d178725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40354 q ha hb
    | true =>
      simp only [d16960, d178725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40355 q ha hb
  have h2 (q : Pattern) (ha : d128358 q = 1) (hb : d159762 q = 1) : d178726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d178726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128358, d178726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16966 q = 1) (hb : d159762 q = 1) : d178728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d178728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40356 q ha hb
    | true =>
      simp only [d16966, d178728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16967 q = 1) (hb : d159762 q = 1) : d178729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d178729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16967, d178729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128359 q = 1) (hb : d159762 q = 1) : d178730 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d178730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128359, d178730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128367 q = 1) (hb : d159762 q = 1) : d178751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128367, d178751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128367, d178751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128368 q = 1) (hb : d159762 q = 1) : d178752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128368, d178752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128368, d178752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d159762 q = 1) : d178753 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d178753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d178753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40359 (p : Pattern) (ha : d15417 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6500 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6500, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15416 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15417 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15417, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40360 (p : Pattern) (ha : d17010 p = 1) (hb : d159762 p = 1) : d178762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1856 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17007 q = 1) (hb : d100904 q = 1) : d17007 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17008 q = 1) (hb : d159761 q = 1) : d178761 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d159761, d178761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17008, d159761, d178761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17009 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17010 q = 1) (hb : d159762 q = 1) : d178762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d159762, d178762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17010, d159762, d178762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40361 (p : Pattern) (ha : d17017 p = 1) (hb : d159762 p = 1) : d178764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17014 q = 1) (hb : d100904 q = 1) : d17014 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17015 q = 1) (hb : d159761 q = 1) : d178763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d159761, d178763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17015, d159761, d178763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17016 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17017 q = 1) (hb : d159762 q = 1) : d178764 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d159762, d178764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17017, d159762, d178764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40362 (p : Pattern) (ha : d17022 p = 1) (hb : d159762 p = 1) : d178769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13489 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15400 q = 1) (hb : d100904 q = 1) : d15400 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17021 q = 1) (hb : d159761 q = 1) : d178768 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d159761, d178768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17021, d159761, d178768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15401 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17022 q = 1) (hb : d159762 q = 1) : d178769 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d159762, d178769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17022, d159762, d178769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40363 (p : Pattern) (ha : d17041 p = 1) (hb : d159762 p = 1) : d178784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d159762 q = 1) : d178765 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d178765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40360 q ha hb
    | true =>
      simp only [d17018, d178765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40361 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d159762 q = 1) : d178766 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d178766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d178766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d159762 q = 1) : d178767 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d178767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d178767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d159762 q = 1) : d178770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d178770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40361 q ha hb
    | true =>
      simp only [d17023, d178770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40362 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d159762 q = 1) : d178771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d178771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d178771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d159762 q = 1) : d178772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d178772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d178772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d159762 q = 1) : d178773 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d178773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d178773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d159762 q = 1) : d178776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40361 q ha hb
    | true =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d159762 q = 1) : d178777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d159762 q = 1) : d178778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17036 q = 1) (hb : d159762 q = 1) : d178779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
    | true =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40359 q ha hb
  have h12 (q : Pattern) (ha : d17037 q = 1) (hb : d159762 q = 1) : d178780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17038 q = 1) (hb : d159762 q = 1) : d178781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17039 q = 1) (hb : d159762 q = 1) : d178782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17040 q = 1) (hb : d159762 q = 1) : d178783 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d178783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d178783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17041 q = 1) (hb : d159762 q = 1) : d178784 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17041, d178784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17041, d178784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40364 (p : Pattern) (ha : d17046 p = 1) (hb : d159762 p = 1) : d178789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d159762 q = 1) : d178776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40361 q ha hb
    | true =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d159762 q = 1) : d178777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d159762 q = 1) : d178778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d159762 q = 1) : d178779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
    | true =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40359 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d159762 q = 1) : d178780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d159762 q = 1) : d178781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d159762 q = 1) : d178782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17044 q = 1) (hb : d159762 q = 1) : d178787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17044, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17045 q = 1) (hb : d159762 q = 1) : d178788 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d178788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17045, d178788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17046 q = 1) (hb : d159762 q = 1) : d178789 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17046, d178789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17046, d178789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40365 (p : Pattern) (ha : d17052 p = 1) (hb : d159762 p = 1) : d178795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17042 q = 1) (hb : d159762 q = 1) : d178785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17042, d178785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40363 q ha hb
    | true =>
      simp only [d17042, d178785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17043 q = 1) (hb : d159762 q = 1) : d178786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17043, d178786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17043, d178786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17047 q = 1) (hb : d159762 q = 1) : d178790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40364 q ha hb
    | true =>
      simp only [d17047, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17048 q = 1) (hb : d159762 q = 1) : d178791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17049 q = 1) (hb : d159762 q = 1) : d178792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17049, d178792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17049, d178792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17050 q = 1) (hb : d159762 q = 1) : d178793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17050, d178793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17050, d178793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17051 q = 1) (hb : d159762 q = 1) : d178794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17051, d178794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17051, d178794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17052 q = 1) (hb : d159762 q = 1) : d178795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17052, d178795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17052, d178795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40366 (p : Pattern) (ha : d17064 p = 1) (hb : d159762 p = 1) : d178803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17047 q = 1) (hb : d159762 q = 1) : d178790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40364 q ha hb
    | true =>
      simp only [d17047, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17048 q = 1) (hb : d159762 q = 1) : d178791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d159762 q = 1) : d178798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d178798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40336 q ha hb
    | true =>
      simp only [d17059, d178798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d159762 q = 1) : d178799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d178799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d178799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17061 q = 1) (hb : d159762 q = 1) : d178800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17061, d178800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17061, d178800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17062 q = 1) (hb : d159762 q = 1) : d178801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17062, d178801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17062, d178801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17063 q = 1) (hb : d159762 q = 1) : d178802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17063, d178802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17063, d178802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17064 q = 1) (hb : d159762 q = 1) : d178803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17064, d178803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17064, d178803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40367 (p : Pattern) (ha : d17113 p = 1) (hb : d159762 p = 1) : d178789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d159762 q = 1) : d178776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40361 q ha hb
    | true =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d159762 q = 1) : d178777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d159762 q = 1) : d178778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d159762 q = 1) : d178779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
    | true =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40359 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d159762 q = 1) : d178780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d159762 q = 1) : d178781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d159762 q = 1) : d178782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17108 q = 1) (hb : d159762 q = 1) : d178779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
    | true =>
      simp only [d17108, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31616 q ha hb
  have h9 (q : Pattern) (ha : d17109 q = 1) (hb : d159762 q = 1) : d178780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17110 q = 1) (hb : d159762 q = 1) : d178781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17111 q = 1) (hb : d159762 q = 1) : d178787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17111, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17112 q = 1) (hb : d159762 q = 1) : d178788 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d178788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17112, d178788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17113 q = 1) (hb : d159762 q = 1) : d178789 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17113, d178789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17113, d178789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40368 (p : Pattern) (ha : d17119 p = 1) (hb : d159762 p = 1) : d178809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17114 q = 1) (hb : d159762 q = 1) : d178790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17114, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40367 q ha hb
    | true =>
      simp only [d17114, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17115 q = 1) (hb : d159762 q = 1) : d178791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17115, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17115, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17116 q = 1) (hb : d159762 q = 1) : d178806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17116, d178806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17116, d178806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17117 q = 1) (hb : d159762 q = 1) : d178807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17117, d178807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17117, d178807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17118 q = 1) (hb : d159762 q = 1) : d178808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17118, d178808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17118, d178808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17119 q = 1) (hb : d159762 q = 1) : d178809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17119, d178809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17119, d178809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40369 (p : Pattern) (ha : d128379 p = 1) (hb : d159762 p = 1) : d178815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17065 q = 1) (hb : d159762 q = 1) : d178804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17065, d178804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40365 q ha hb
    | true =>
      simp only [d17065, d178804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40366 q ha hb
  have h2 (q : Pattern) (ha : d128375 q = 1) (hb : d159762 q = 1) : d178805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d178805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128375, d178805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17120 q = 1) (hb : d159762 q = 1) : d178810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17120, d178810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40368 q ha hb
    | true =>
      simp only [d17120, d178810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17121 q = 1) (hb : d159762 q = 1) : d178811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17121, d178811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17121, d178811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d159762 q = 1) : d178812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d178812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128376, d178812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d159762 q = 1) : d178813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d178813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d178813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d159762 q = 1) : d178814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d178814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d178814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d159762 q = 1) : d178815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d178815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d178815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40370 (p : Pattern) (ha : d128385 p = 1) (hb : d159762 p = 1) : d178832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16829 q = 1) (hb : d159762 q = 1) : d178652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16829, d178652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16829, d178652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40325 q ha hb
  have h2 (q : Pattern) (ha : d16830 q = 1) (hb : d159762 q = 1) : d178653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16830, d178653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16830, d178653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16839 q = 1) (hb : d159762 q = 1) : d178662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d178662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40325 q ha hb
    | true =>
      simp only [d16839, d178662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40328 q ha hb
  have h4 (q : Pattern) (ha : d16840 q = 1) (hb : d159762 q = 1) : d178663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d178663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16840, d178663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16841 q = 1) (hb : d159762 q = 1) : d178664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16841, d178664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16841, d178664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128363 q = 1) (hb : d159762 q = 1) : d178734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128363, d178734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40349 q ha hb
    | true =>
      simp only [d128363, d178734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40357 q ha hb
  have h7 (q : Pattern) (ha : d16990 q = 1) (hb : d159762 q = 1) : d178747 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16990, d178747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40331 q ha hb
    | true =>
      simp only [d16990, d178747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40332 q ha hb
  have h8 (q : Pattern) (ha : d128364 q = 1) (hb : d159762 q = 1) : d178748 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128364, d178748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128364, d178748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128365 q = 1) (hb : d159762 q = 1) : d178749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d178749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128365, d178749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128366 q = 1) (hb : d159762 q = 1) : d178750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d178750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128366, d178750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128370 q = 1) (hb : d159762 q = 1) : d178754 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d178754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128370, d178754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40358 q ha hb
  have h12 (q : Pattern) (ha : d16999 q = 1) (hb : d159762 q = 1) : d178756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16999, d178756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16999, d178756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40333 q ha hb
  have h13 (q : Pattern) (ha : d128371 q = 1) (hb : d159762 q = 1) : d178757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d178757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128371, d178757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128372 q = 1) (hb : d159762 q = 1) : d178758 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d178758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128372, d178758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128373 q = 1) (hb : d159762 q = 1) : d178759 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d178759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128373, d178759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128374 q = 1) (hb : d159762 q = 1) : d178760 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d178760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128374, d178760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128380 q = 1) (hb : d159762 q = 1) : d178816 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d178816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128380, d178816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40369 q ha hb
  have h18 (q : Pattern) (ha : d17137 q = 1) (hb : d159762 q = 1) : d178827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17137, d178827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17137, d178827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40338 q ha hb
  have h19 (q : Pattern) (ha : d128381 q = 1) (hb : d159762 q = 1) : d178828 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d178828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128381, d178828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128382 q = 1) (hb : d159762 q = 1) : d178829 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d178829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128382, d178829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128383 q = 1) (hb : d159762 q = 1) : d178830 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d178830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128383, d178830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128384 q = 1) (hb : d159762 q = 1) : d178831 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d178831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128384, d178831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128385 q = 1) (hb : d159762 q = 1) : d178832 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d178832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128385, d178832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40371 (p : Pattern) (ha : d128391 p = 1) (hb : d159762 p = 1) : d178838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d159762 q = 1) : d178833 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d178833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d178833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40370 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d159762 q = 1) : d178834 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d178834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d178834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d159762 q = 1) : d178835 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d178835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d178835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d159762 q = 1) : d178836 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d178836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d178836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d159762 q = 1) : d178837 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d178837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d178837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d159762 q = 1) : d178838 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d178838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d178838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40372 (p : Pattern) (ha : d15558 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5251 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5251, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15558 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15558, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40373 (p : Pattern) (ha : d15563 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2068 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2071 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2071, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15557 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15563 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15563, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40374 (p : Pattern) (ha : d17157 p = 1) (hb : d159762 p = 1) : d178844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2038 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17154 q = 1) (hb : d100904 q = 1) : d17154 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17155 q = 1) (hb : d159761 q = 1) : d178843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d159761, d178843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17155, d159761, d178843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17156 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17157 q = 1) (hb : d159762 q = 1) : d178844 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, d159762, d178844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17157, d159762, d178844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40375 (p : Pattern) (ha : d17161 p = 1) (hb : d159762 p = 1) : d178846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17159 q = 1) (hb : d100904 q = 1) : d17159 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17160 q = 1) (hb : d159761 q = 1) : d178845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, d159761, d178845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17160, d159761, d178845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15550 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17161 q = 1) (hb : d159762 q = 1) : d178846 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, d159762, d178846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17161, d159762, d178846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40376 (p : Pattern) (ha : d17174 p = 1) (hb : d159762 p = 1) : d178856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d159762 q = 1) : d178847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40374 q ha hb
    | true =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d159762 q = 1) : d178848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d159762 q = 1) : d178849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d159762 q = 1) : d178850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
    | true =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40372 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d159762 q = 1) : d178851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d159762 q = 1) : d178852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d159762 q = 1) : d178853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17169 q = 1) (hb : d159762 q = 1) : d178850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
    | true =>
      simp only [d17169, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40373 q ha hb
  have h9 (q : Pattern) (ha : d17170 q = 1) (hb : d159762 q = 1) : d178851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17171 q = 1) (hb : d159762 q = 1) : d178852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17172 q = 1) (hb : d159762 q = 1) : d178854 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17172, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17173 q = 1) (hb : d159762 q = 1) : d178855 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17173, d178855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17173, d178855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17174 q = 1) (hb : d159762 q = 1) : d178856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17174, d178856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17174, d178856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40377 (p : Pattern) (ha : d17178 p = 1) (hb : d159762 p = 1) : d178860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17169 q = 1) (hb : d159762 q = 1) : d178850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
    | true =>
      simp only [d17169, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40373 q ha hb
  have h2 (q : Pattern) (ha : d17170 q = 1) (hb : d159762 q = 1) : d178851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17171 q = 1) (hb : d159762 q = 1) : d178852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17172 q = 1) (hb : d159762 q = 1) : d178854 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17172, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17177 q = 1) (hb : d159762 q = 1) : d178859 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17177, d178859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17177, d178859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17178 q = 1) (hb : d159762 q = 1) : d178860 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17178, d178860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17178, d178860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40378 (p : Pattern) (ha : d17184 p = 1) (hb : d159762 p = 1) : d178866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40376 q ha hb
    | true =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d159762 q = 1) : d178864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d159762 q = 1) : d178865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17184 q = 1) (hb : d159762 q = 1) : d178866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17184, d178866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17184, d178866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40379 (p : Pattern) (ha : d17188 p = 1) (hb : d159762 p = 1) : d178870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d159762 q = 1) : d178867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d159762 q = 1) : d178868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d159762 q = 1) : d178869 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d178869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d178869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17188 q = 1) (hb : d159762 q = 1) : d178870 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17188, d178870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17188, d178870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40380 (p : Pattern) (ha : d17194 p = 1) (hb : d159762 p = 1) : d178876 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d159762 q = 1) : d178871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d178871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40378 q ha hb
    | true =>
      simp only [d17189, d178871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40379 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d159762 q = 1) : d178872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d178872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d178872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d159762 q = 1) : d178873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d178873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d178873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d159762 q = 1) : d178874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d178874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d178874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d159762 q = 1) : d178875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d178875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d178875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17194 q = 1) (hb : d159762 q = 1) : d178876 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17194, d178876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17194, d178876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40381 (p : Pattern) (ha : d17197 p = 1) (hb : d159762 p = 1) : d178879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40376 q ha hb
    | true =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d159762 q = 1) : d178864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d159762 q = 1) : d178865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17197 q = 1) (hb : d159762 q = 1) : d178879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17197, d178879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17197, d178879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40382 (p : Pattern) (ha : d17198 p = 1) (hb : d159762 p = 1) : d178880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d159762 q = 1) : d178867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d159762 q = 1) : d178868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d159762 q = 1) : d178869 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d178869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d178869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17198 q = 1) (hb : d159762 q = 1) : d178880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17198, d178880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17198, d178880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40383 (p : Pattern) (ha : d17204 p = 1) (hb : d159762 p = 1) : d178886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d159762 q = 1) : d178871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d178871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40378 q ha hb
    | true =>
      simp only [d17189, d178871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40379 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d159762 q = 1) : d178872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d178872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d178872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d159762 q = 1) : d178873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d178873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d178873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d159762 q = 1) : d178874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d178874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d178874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d159762 q = 1) : d178875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d178875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d178875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17199 q = 1) (hb : d159762 q = 1) : d178881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d178881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40381 q ha hb
    | true =>
      simp only [d17199, d178881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40382 q ha hb
  have h7 (q : Pattern) (ha : d17200 q = 1) (hb : d159762 q = 1) : d178882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d178882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d178882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17201 q = 1) (hb : d159762 q = 1) : d178883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d178883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17201, d178883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17202 q = 1) (hb : d159762 q = 1) : d178884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d178884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d178884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17203 q = 1) (hb : d159762 q = 1) : d178885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d178885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d178885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17204 q = 1) (hb : d159762 q = 1) : d178886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17204, d178886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17204, d178886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40384 (p : Pattern) (ha : d17244 p = 1) (hb : d159762 p = 1) : d178856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d159762 q = 1) : d178847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40374 q ha hb
    | true =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d159762 q = 1) : d178848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d159762 q = 1) : d178849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d159762 q = 1) : d178850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
    | true =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40372 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d159762 q = 1) : d178851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d159762 q = 1) : d178852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d159762 q = 1) : d178853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17242 q = 1) (hb : d159762 q = 1) : d178854 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17242, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17242, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17243 q = 1) (hb : d159762 q = 1) : d178855 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17243, d178855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17243, d178855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17244 q = 1) (hb : d159762 q = 1) : d178856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17244, d178856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17244, d178856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40385 (p : Pattern) (ha : d17254 p = 1) (hb : d159762 p = 1) : d178866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40384 q ha hb
    | true =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d159762 q = 1) : d178864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d159762 q = 1) : d178865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17254 q = 1) (hb : d159762 q = 1) : d178866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17254, d178866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17254, d178866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40386 (p : Pattern) (ha : d17348 p = 1) (hb : d159762 p = 1) : d178963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17338 q = 1) (hb : d159762 q = 1) : d178871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17338, d178871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40385 q ha hb
    | true =>
      simp only [d17338, d178871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40379 q ha hb
  have h2 (q : Pattern) (ha : d17339 q = 1) (hb : d159762 q = 1) : d178872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17339, d178872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17339, d178872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17340 q = 1) (hb : d159762 q = 1) : d178873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17340, d178873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17340, d178873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17341 q = 1) (hb : d159762 q = 1) : d178874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17341, d178874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17341, d178874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17342 q = 1) (hb : d159762 q = 1) : d178875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17342, d178875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17342, d178875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17343 q = 1) (hb : d159762 q = 1) : d178958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d178958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40379 q ha hb
    | true =>
      simp only [d17343, d178958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17344 q = 1) (hb : d159762 q = 1) : d178959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d178959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d178959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17345 q = 1) (hb : d159762 q = 1) : d178960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d178960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17345, d178960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17346 q = 1) (hb : d159762 q = 1) : d178961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d178961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d178961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17347 q = 1) (hb : d159762 q = 1) : d178962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d178962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d178962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17348 q = 1) (hb : d159762 q = 1) : d178963 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17348, d178963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17348, d178963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40387 (p : Pattern) (ha : d17354 p = 1) (hb : d159762 p = 1) : d178969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17343 q = 1) (hb : d159762 q = 1) : d178958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d178958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40379 q ha hb
    | true =>
      simp only [d17343, d178958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17344 q = 1) (hb : d159762 q = 1) : d178959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d178959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d178959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17345 q = 1) (hb : d159762 q = 1) : d178960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d178960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17345, d178960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17346 q = 1) (hb : d159762 q = 1) : d178961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d178961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d178961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17347 q = 1) (hb : d159762 q = 1) : d178962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d178962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d178962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17349 q = 1) (hb : d159762 q = 1) : d178964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d178964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40382 q ha hb
    | true =>
      simp only [d17349, d178964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17350 q = 1) (hb : d159762 q = 1) : d178965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d178965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d178965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17351 q = 1) (hb : d159762 q = 1) : d178966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d178966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17351, d178966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17352 q = 1) (hb : d159762 q = 1) : d178967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d178967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d178967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17353 q = 1) (hb : d159762 q = 1) : d178968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d178968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d178968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17354 q = 1) (hb : d159762 q = 1) : d178969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17354, d178969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17354, d178969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40388 (p : Pattern) (ha : d17363 p = 1) (hb : d159762 p = 1) : d178978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17349 q = 1) (hb : d159762 q = 1) : d178964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d178964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40382 q ha hb
    | true =>
      simp only [d17349, d178964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17350 q = 1) (hb : d159762 q = 1) : d178965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d178965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d178965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17351 q = 1) (hb : d159762 q = 1) : d178966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d178966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17351, d178966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17352 q = 1) (hb : d159762 q = 1) : d178967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d178967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d178967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17353 q = 1) (hb : d159762 q = 1) : d178968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d178968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d178968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17363 q = 1) (hb : d159762 q = 1) : d178978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17363, d178978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17363, d178978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40389 (p : Pattern) (ha : d15813 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2349 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2355 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2355, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15813 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15813, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40390 (p : Pattern) (ha : d17396 p = 1) (hb : d159762 p = 1) : d178996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2343 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17394 q = 1) (hb : d100904 q = 1) : d17394 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17395 q = 1) (hb : d159761 q = 1) : d178995 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d159761, d178995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17395, d159761, d178995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15779 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17396 q = 1) (hb : d159762 q = 1) : d178996 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d159762, d178996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17396, d159762, d178996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40391 (p : Pattern) (ha : d17422 p = 1) (hb : d159762 p = 1) : d179018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17417 q = 1) (hb : d159762 q = 1) : d179000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
    | true =>
      simp only [d17417, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40389 q ha hb
  have h2 (q : Pattern) (ha : d17418 q = 1) (hb : d159762 q = 1) : d179001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17419 q = 1) (hb : d159762 q = 1) : d179002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17420 q = 1) (hb : d159762 q = 1) : d179008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17420, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17421 q = 1) (hb : d159762 q = 1) : d179017 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d179017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17421, d179017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17422 q = 1) (hb : d159762 q = 1) : d179018 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17422, d179018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17422, d179018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40392 (p : Pattern) (ha : d17494 p = 1) (hb : d159762 p = 1) : d179041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17423 q = 1) (hb : d159762 q = 1) : d179019 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d179019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40391 q ha hb
    | true =>
      simp only [d17423, d179019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17424 q = 1) (hb : d159762 q = 1) : d179020 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d179020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d179020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17491 q = 1) (hb : d159762 q = 1) : d179038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17491, d179038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17491, d179038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17492 q = 1) (hb : d159762 q = 1) : d179039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17492, d179039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17492, d179039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17493 q = 1) (hb : d159762 q = 1) : d179040 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17493, d179040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17493, d179040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17494 q = 1) (hb : d159762 q = 1) : d179041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17494, d179041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17494, d179041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40393 (p : Pattern) (ha : d17500 p = 1) (hb : d159762 p = 1) : d179047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17495 q = 1) (hb : d159762 q = 1) : d179042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17495, d179042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40392 q ha hb
    | true =>
      simp only [d17495, d179042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17496 q = 1) (hb : d159762 q = 1) : d179043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17496, d179043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17496, d179043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17497 q = 1) (hb : d159762 q = 1) : d179044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17497, d179044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17497, d179044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17498 q = 1) (hb : d159762 q = 1) : d179045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17498, d179045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17498, d179045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17499 q = 1) (hb : d159762 q = 1) : d179046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17499, d179046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17499, d179046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17500 q = 1) (hb : d159762 q = 1) : d179047 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17500, d179047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17500, d179047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40394 (p : Pattern) (ha : d17209 p = 1) (hb : d159762 p = 1) : d178891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40376 q ha hb
    | true =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d159762 q = 1) : d178864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d159762 q = 1) : d178890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d178890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d178890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17209 q = 1) (hb : d159762 q = 1) : d178891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17209, d178891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17209, d178891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40395 (p : Pattern) (ha : d17211 p = 1) (hb : d159762 p = 1) : d178893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d159762 q = 1) : d178867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d159762 q = 1) : d178868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d159762 q = 1) : d178892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d178892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d178892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17211 q = 1) (hb : d159762 q = 1) : d178893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17211, d178893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17211, d178893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40396 (p : Pattern) (ha : d17218 p = 1) (hb : d159762 p = 1) : d178900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40376 q ha hb
    | true =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d159762 q = 1) : d178898 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d178898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d178898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d159762 q = 1) : d178899 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d178899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d178899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17218 q = 1) (hb : d159762 q = 1) : d178900 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17218, d178900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17218, d178900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40397 (p : Pattern) (ha : d17221 p = 1) (hb : d159762 p = 1) : d178903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d159762 q = 1) : d178867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d159762 q = 1) : d178901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d178901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d178901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d159762 q = 1) : d178902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d178902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d178902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17221 q = 1) (hb : d159762 q = 1) : d178903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17221, d178903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17221, d178903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40398 (p : Pattern) (ha : d17229 p = 1) (hb : d159762 p = 1) : d149593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17226 q = 1) (hb : d100904 q = 1) : d17226 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17227 q = 1) (hb : d159761 q = 1) : d22767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, d159761, d22767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17227, d159761, d22767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17228 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17229 q = 1) (hb : d159762 q = 1) : d149593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, d159762, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17229, d159762, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40399 (p : Pattern) (ha : d17233 p = 1) (hb : d159762 p = 1) : d178911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15549 q = 1) (hb : d100904 q = 1) : d15549 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17156 q = 1) (hb : d159761 q = 1) : d178910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d159761, d178910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17156, d159761, d178910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15550 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17233 q = 1) (hb : d159762 q = 1) : d178911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, d159762, d178911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17233, d159762, d178911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40400 (p : Pattern) (ha : d17239 p = 1) (hb : d159762 p = 1) : d178917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d159762 q = 1) : d178907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d178907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40398 q ha hb
    | true =>
      simp only [d17230, d178907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40374 q ha hb
  have h2 (q : Pattern) (ha : d17231 q = 1) (hb : d159762 q = 1) : d178908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17231, d178908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17231, d178908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17232 q = 1) (hb : d159762 q = 1) : d178909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17232, d178909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17232, d178909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d159762 q = 1) : d178912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d178912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40374 q ha hb
    | true =>
      simp only [d17234, d178912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40399 q ha hb
  have h5 (q : Pattern) (ha : d17235 q = 1) (hb : d159762 q = 1) : d178913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17235, d178913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17235, d178913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17236 q = 1) (hb : d159762 q = 1) : d178914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17236, d178914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17236, d178914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17237 q = 1) (hb : d159762 q = 1) : d178915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17237, d178915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17237, d178915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d159762 q = 1) : d178847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40374 q ha hb
    | true =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
  have h9 (q : Pattern) (ha : d17163 q = 1) (hb : d159762 q = 1) : d178848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17164 q = 1) (hb : d159762 q = 1) : d178849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17165 q = 1) (hb : d159762 q = 1) : d178850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
    | true =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40372 q ha hb
  have h12 (q : Pattern) (ha : d17166 q = 1) (hb : d159762 q = 1) : d178851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17167 q = 1) (hb : d159762 q = 1) : d178852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17168 q = 1) (hb : d159762 q = 1) : d178853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17238 q = 1) (hb : d159762 q = 1) : d178916 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17238, d178916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17238, d178916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17239 q = 1) (hb : d159762 q = 1) : d178917 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17239, d178917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17239, d178917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40401 (p : Pattern) (ha : d17250 p = 1) (hb : d159762 p = 1) : d178923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d159762 q = 1) : d178918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d178918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40400 q ha hb
    | true =>
      simp only [d17240, d178918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d159762 q = 1) : d178919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d178919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d178919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40384 q ha hb
    | true =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d159762 q = 1) : d178920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d178920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d178920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d159762 q = 1) : d178921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d178921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d178921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d159762 q = 1) : d178922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d178922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d178922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17250 q = 1) (hb : d159762 q = 1) : d178923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17250, d178923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17250, d178923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40402 (p : Pattern) (ha : d17299 p = 1) (hb : d159762 p = 1) : d178856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d159762 q = 1) : d178847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40374 q ha hb
    | true =>
      simp only [d17162, d178847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d159762 q = 1) : d178848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d178848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d159762 q = 1) : d178849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d178849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d159762 q = 1) : d178850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
    | true =>
      simp only [d17165, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40372 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d159762 q = 1) : d178851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d159762 q = 1) : d178852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d159762 q = 1) : d178853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d178853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17294 q = 1) (hb : d159762 q = 1) : d178850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40375 q ha hb
    | true =>
      simp only [d17294, d178850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31655 q ha hb
  have h9 (q : Pattern) (ha : d17295 q = 1) (hb : d159762 q = 1) : d178851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17295, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17295, d178851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17296 q = 1) (hb : d159762 q = 1) : d178852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17296, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17296, d178852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17297 q = 1) (hb : d159762 q = 1) : d178854 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17297, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17297, d178854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17298 q = 1) (hb : d159762 q = 1) : d178855 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17298, d178855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17298, d178855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17299 q = 1) (hb : d159762 q = 1) : d178856 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17299, d178856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17299, d178856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40403 (p : Pattern) (ha : d17305 p = 1) (hb : d159762 p = 1) : d178929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40402 q ha hb
    | true =>
      simp only [d17300, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d159762 q = 1) : d178926 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d178926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d178926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d159762 q = 1) : d178927 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d178927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d178927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d159762 q = 1) : d178928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d178928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d178928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17305 q = 1) (hb : d159762 q = 1) : d178929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17305, d178929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17305, d178929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40404 (p : Pattern) (ha : d128400 p = 1) (hb : d159762 p = 1) : d178935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d159762 q = 1) : d178894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d178894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40394 q ha hb
    | true =>
      simp only [d17212, d178894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40395 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d159762 q = 1) : d178895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d178895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d178895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d159762 q = 1) : d178896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d178896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d178896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d159762 q = 1) : d178897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d178897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d178897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d159762 q = 1) : d178904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d178904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40396 q ha hb
    | true =>
      simp only [d17222, d178904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40397 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d159762 q = 1) : d178905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d178905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d178905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d159762 q = 1) : d178906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d178906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d178906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d159762 q = 1) : d178924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d178924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40401 q ha hb
    | true =>
      simp only [d17255, d178924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40385 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d159762 q = 1) : d178925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d178925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d178925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d159762 q = 1) : d178930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d178930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40403 q ha hb
    | true =>
      simp only [d17306, d178930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d159762 q = 1) : d178931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d178931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d178931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d159762 q = 1) : d178932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d178932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d178932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d159762 q = 1) : d178933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d178933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d178933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d159762 q = 1) : d178934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d178934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d178934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128400 q = 1) (hb : d159762 q = 1) : d178935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128400, d178935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128400, d178935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40405 (p : Pattern) (ha : d17312 p = 1) (hb : d159762 p = 1) : d178936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40376 q ha hb
    | true =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d159762 q = 1) : d178864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d159762 q = 1) : d178890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d178890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d178890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17312 q = 1) (hb : d159762 q = 1) : d178936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17312, d178936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17312, d178936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40406 (p : Pattern) (ha : d17313 p = 1) (hb : d159762 p = 1) : d178937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d159762 q = 1) : d178867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d159762 q = 1) : d178868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d178868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d159762 q = 1) : d178892 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d178892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d178892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17313 q = 1) (hb : d159762 q = 1) : d178937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17313, d178937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17313, d178937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40407 (p : Pattern) (ha : d17318 p = 1) (hb : d159762 p = 1) : d178942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40376 q ha hb
    | true =>
      simp only [d17175, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d159762 q = 1) : d178898 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d178898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d178898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d159762 q = 1) : d178899 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d178899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d178899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17318 q = 1) (hb : d159762 q = 1) : d178942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17318, d178942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17318, d178942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40408 (p : Pattern) (ha : d17319 p = 1) (hb : d159762 p = 1) : d178943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d159762 q = 1) : d178867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d178867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d159762 q = 1) : d178901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d178901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d178901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d159762 q = 1) : d178902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d178902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d178902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17319 q = 1) (hb : d159762 q = 1) : d178943 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17319, d178943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17319, d178943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40409 (p : Pattern) (ha : d17323 p = 1) (hb : d159762 p = 1) : d178947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d159762 q = 1) : d178918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d178918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40400 q ha hb
    | true =>
      simp only [d17240, d178918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d159762 q = 1) : d178919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d178919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d178919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40384 q ha hb
    | true =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d159762 q = 1) : d178920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d178920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d178920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d159762 q = 1) : d178921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d178921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d178921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d159762 q = 1) : d178922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d178922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d178922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17323 q = 1) (hb : d159762 q = 1) : d178947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17323, d178947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17323, d178947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40410 (p : Pattern) (ha : d17324 p = 1) (hb : d159762 p = 1) : d178879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40384 q ha hb
    | true =>
      simp only [d17245, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d159762 q = 1) : d178861 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40377 q ha hb
    | true =>
      simp only [d17179, d178861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d159762 q = 1) : d178862 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d178862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d159762 q = 1) : d178863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d178863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d159762 q = 1) : d178864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d178864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d159762 q = 1) : d178865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d178865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17324 q = 1) (hb : d159762 q = 1) : d178879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17324, d178879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17324, d178879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40411 (p : Pattern) (ha : d17330 p = 1) (hb : d159762 p = 1) : d178950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d159762 q = 1) : d178857 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40402 q ha hb
    | true =>
      simp only [d17300, d178857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d159762 q = 1) : d178858 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d178858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d159762 q = 1) : d178926 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d178926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d178926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d159762 q = 1) : d178927 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d178927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d178927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d159762 q = 1) : d178928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d178928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d178928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17330 q = 1) (hb : d159762 q = 1) : d178950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17330, d178950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17330, d178950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40412 (p : Pattern) (ha : d128405 p = 1) (hb : d159762 p = 1) : d178956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d159762 q = 1) : d178894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d178894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40394 q ha hb
    | true =>
      simp only [d17212, d178894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40395 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d159762 q = 1) : d178895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d178895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d178895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d159762 q = 1) : d178896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d178896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d178896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d159762 q = 1) : d178897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d178897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d178897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d159762 q = 1) : d178904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d178904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40396 q ha hb
    | true =>
      simp only [d17222, d178904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40397 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d159762 q = 1) : d178905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d178905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d178905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d159762 q = 1) : d178906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d178906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d178906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d159762 q = 1) : d178924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d178924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40401 q ha hb
    | true =>
      simp only [d17255, d178924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40385 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d159762 q = 1) : d178925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d178925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d178925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d159762 q = 1) : d178930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d178930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40403 q ha hb
    | true =>
      simp only [d17306, d178930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d159762 q = 1) : d178931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d178931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d178931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d159762 q = 1) : d178932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d178932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d178932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d159762 q = 1) : d178933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d178933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d178933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d159762 q = 1) : d178934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d178934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d178934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17314 q = 1) (hb : d159762 q = 1) : d178938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17314, d178938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40405 q ha hb
    | true =>
      simp only [d17314, d178938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40406 q ha hb
  have h16 (q : Pattern) (ha : d17315 q = 1) (hb : d159762 q = 1) : d178939 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17315, d178939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17315, d178939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17316 q = 1) (hb : d159762 q = 1) : d178940 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17316, d178940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17316, d178940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d17317 q = 1) (hb : d159762 q = 1) : d178941 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17317, d178941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17317, d178941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17320 q = 1) (hb : d159762 q = 1) : d178944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17320, d178944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40407 q ha hb
    | true =>
      simp only [d17320, d178944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40408 q ha hb
  have h20 (q : Pattern) (ha : d17321 q = 1) (hb : d159762 q = 1) : d178945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17321, d178945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17321, d178945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17322 q = 1) (hb : d159762 q = 1) : d178946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17322, d178946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17322, d178946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d17325 q = 1) (hb : d159762 q = 1) : d178948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d178948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40409 q ha hb
    | true =>
      simp only [d17325, d178948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40410 q ha hb
  have h23 (q : Pattern) (ha : d128401 q = 1) (hb : d159762 q = 1) : d178949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d178949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128401, d178949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d17331 q = 1) (hb : d159762 q = 1) : d178951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d178951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40411 q ha hb
    | true =>
      simp only [d17331, d178951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d17332 q = 1) (hb : d159762 q = 1) : d178952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d178952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17332, d178952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128402 q = 1) (hb : d159762 q = 1) : d178953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d178953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128402, d178953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128403 q = 1) (hb : d159762 q = 1) : d178954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128403, d178954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128403, d178954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128404 q = 1) (hb : d159762 q = 1) : d178955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128404, d178955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128404, d178955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128405 q = 1) (hb : d159762 q = 1) : d178956 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128405, d178956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128405, d178956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro40413 (p : Pattern) (ha : d128412 p = 1) (hb : d159762 p = 1) : d178976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17325 q = 1) (hb : d159762 q = 1) : d178948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d178948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40409 q ha hb
    | true =>
      simp only [d17325, d178948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40410 q ha hb
  have h2 (q : Pattern) (ha : d128401 q = 1) (hb : d159762 q = 1) : d178949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d178949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128401, d178949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17331 q = 1) (hb : d159762 q = 1) : d178951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d178951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40411 q ha hb
    | true =>
      simp only [d17331, d178951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17332 q = 1) (hb : d159762 q = 1) : d178952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d178952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17332, d178952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128402 q = 1) (hb : d159762 q = 1) : d178953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d178953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128402, d178953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128410 q = 1) (hb : d159762 q = 1) : d178974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128410, d178974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128410, d178974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128411 q = 1) (hb : d159762 q = 1) : d178975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128411, d178975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128411, d178975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d159762 q = 1) : d178976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d178976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d178976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40414 (p : Pattern) (ha : d15795 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6647 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6647, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15795, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40415 (p : Pattern) (ha : d17375 p = 1) (hb : d159762 p = 1) : d149666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17372 q = 1) (hb : d100904 q = 1) : d17372 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17373 q = 1) (hb : d159761 q = 1) : d22930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d159761, d22930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17373, d159761, d22930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17374 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17375 q = 1) (hb : d159762 q = 1) : d149666 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d159762, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17375, d159762, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40416 (p : Pattern) (ha : d17382 p = 1) (hb : d159762 p = 1) : d178985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17379 q = 1) (hb : d100904 q = 1) : d17379 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17380 q = 1) (hb : d159761 q = 1) : d178984 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d159761, d178984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17380, d159761, d178984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17382 q = 1) (hb : d159762 q = 1) : d178985 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d159762, d178985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17382, d159762, d178985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40417 (p : Pattern) (ha : d17386 p = 1) (hb : d159762 p = 1) : d178990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13816 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15778 q = 1) (hb : d100904 q = 1) : d15778 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17381 q = 1) (hb : d159761 q = 1) : d178989 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d159761, d178989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17381, d159761, d178989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15779 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17386 q = 1) (hb : d159762 q = 1) : d178990 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d159762, d178990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17386, d159762, d178990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40418 (p : Pattern) (ha : d17405 p = 1) (hb : d159762 p = 1) : d179005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d159762 q = 1) : d178986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d178986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40415 q ha hb
    | true =>
      simp only [d17383, d178986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40416 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d159762 q = 1) : d178987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d178987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d178987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d159762 q = 1) : d178988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d178988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d178988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d159762 q = 1) : d178991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d178991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40416 q ha hb
    | true =>
      simp only [d17387, d178991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40417 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d159762 q = 1) : d178992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d178992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d178992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d159762 q = 1) : d178993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d178993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d178993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d159762 q = 1) : d178994 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d178994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d178994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d159762 q = 1) : d178997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40416 q ha hb
    | true =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d159762 q = 1) : d178998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d159762 q = 1) : d178999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17400 q = 1) (hb : d159762 q = 1) : d179000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
    | true =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40414 q ha hb
  have h12 (q : Pattern) (ha : d17401 q = 1) (hb : d159762 q = 1) : d179001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17402 q = 1) (hb : d159762 q = 1) : d179002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17403 q = 1) (hb : d159762 q = 1) : d179003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17404 q = 1) (hb : d159762 q = 1) : d179004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d179004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d179004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17405 q = 1) (hb : d159762 q = 1) : d179005 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17405, d179005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17405, d179005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40419 (p : Pattern) (ha : d17410 p = 1) (hb : d159762 p = 1) : d179010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d159762 q = 1) : d178997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40416 q ha hb
    | true =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d159762 q = 1) : d178998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d159762 q = 1) : d178999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d159762 q = 1) : d179000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
    | true =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40414 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d159762 q = 1) : d179001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d159762 q = 1) : d179002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d159762 q = 1) : d179003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17408 q = 1) (hb : d159762 q = 1) : d179008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17408, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17409 q = 1) (hb : d159762 q = 1) : d179009 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d179009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17409, d179009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17410 q = 1) (hb : d159762 q = 1) : d179010 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17410, d179010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17410, d179010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40420 (p : Pattern) (ha : d17416 p = 1) (hb : d159762 p = 1) : d179016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17406 q = 1) (hb : d159762 q = 1) : d179006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17406, d179006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40418 q ha hb
    | true =>
      simp only [d17406, d179006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17407 q = 1) (hb : d159762 q = 1) : d179007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17407, d179007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17407, d179007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17411 q = 1) (hb : d159762 q = 1) : d179011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40419 q ha hb
    | true =>
      simp only [d17411, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17412 q = 1) (hb : d159762 q = 1) : d179012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17413 q = 1) (hb : d159762 q = 1) : d179013 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17413, d179013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17413, d179013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17414 q = 1) (hb : d159762 q = 1) : d179014 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17414, d179014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17414, d179014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17415 q = 1) (hb : d159762 q = 1) : d179015 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17415, d179015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17415, d179015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17416 q = 1) (hb : d159762 q = 1) : d179016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17416, d179016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17416, d179016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40421 (p : Pattern) (ha : d17428 p = 1) (hb : d159762 p = 1) : d179024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17411 q = 1) (hb : d159762 q = 1) : d179011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40419 q ha hb
    | true =>
      simp only [d17411, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17412 q = 1) (hb : d159762 q = 1) : d179012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d159762 q = 1) : d179019 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d179019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40391 q ha hb
    | true =>
      simp only [d17423, d179019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d159762 q = 1) : d179020 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d179020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d179020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17425 q = 1) (hb : d159762 q = 1) : d179021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17425, d179021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17425, d179021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17426 q = 1) (hb : d159762 q = 1) : d179022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17426, d179022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17426, d179022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17427 q = 1) (hb : d159762 q = 1) : d179023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17427, d179023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17427, d179023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17428 q = 1) (hb : d159762 q = 1) : d179024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17428, d179024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17428, d179024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40422 (p : Pattern) (ha : d17477 p = 1) (hb : d159762 p = 1) : d179010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d159762 q = 1) : d178997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40416 q ha hb
    | true =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d159762 q = 1) : d178998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d159762 q = 1) : d178999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d159762 q = 1) : d179000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
    | true =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40414 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d159762 q = 1) : d179001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d159762 q = 1) : d179002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d159762 q = 1) : d179003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17472 q = 1) (hb : d159762 q = 1) : d179000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
    | true =>
      simp only [d17472, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31670 q ha hb
  have h9 (q : Pattern) (ha : d17473 q = 1) (hb : d159762 q = 1) : d179001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17474 q = 1) (hb : d159762 q = 1) : d179002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17475 q = 1) (hb : d159762 q = 1) : d179008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17475, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17476 q = 1) (hb : d159762 q = 1) : d179009 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d179009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17476, d179009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17477 q = 1) (hb : d159762 q = 1) : d179010 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17477, d179010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17477, d179010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40423 (p : Pattern) (ha : d17483 p = 1) (hb : d159762 p = 1) : d179030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17478 q = 1) (hb : d159762 q = 1) : d179011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17478, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40422 q ha hb
    | true =>
      simp only [d17478, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17479 q = 1) (hb : d159762 q = 1) : d179012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17479, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17479, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17480 q = 1) (hb : d159762 q = 1) : d179027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17480, d179027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17480, d179027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17481 q = 1) (hb : d159762 q = 1) : d179028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17481, d179028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17481, d179028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17482 q = 1) (hb : d159762 q = 1) : d179029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17482, d179029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17482, d179029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17483 q = 1) (hb : d159762 q = 1) : d179030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17483, d179030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17483, d179030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40424 (p : Pattern) (ha : d128422 p = 1) (hb : d159762 p = 1) : d179036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17429 q = 1) (hb : d159762 q = 1) : d179025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17429, d179025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40420 q ha hb
    | true =>
      simp only [d17429, d179025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40421 q ha hb
  have h2 (q : Pattern) (ha : d128418 q = 1) (hb : d159762 q = 1) : d179026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d179026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128418, d179026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17484 q = 1) (hb : d159762 q = 1) : d179031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17484, d179031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40423 q ha hb
    | true =>
      simp only [d17484, d179031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17485 q = 1) (hb : d159762 q = 1) : d179032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17485, d179032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17485, d179032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d159762 q = 1) : d179033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d179033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128419, d179033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d159762 q = 1) : d179034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d179034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d179034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d159762 q = 1) : d179035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d179035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d179035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d159762 q = 1) : d179036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d179036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d179036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40425 (p : Pattern) (ha : d128428 p = 1) (hb : d159762 p = 1) : d179053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17195 q = 1) (hb : d159762 q = 1) : d178877 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17195, d178877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17195, d178877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40380 q ha hb
  have h2 (q : Pattern) (ha : d17196 q = 1) (hb : d159762 q = 1) : d178878 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17196, d178878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17196, d178878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17205 q = 1) (hb : d159762 q = 1) : d178887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d178887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40380 q ha hb
    | true =>
      simp only [d17205, d178887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40383 q ha hb
  have h4 (q : Pattern) (ha : d17206 q = 1) (hb : d159762 q = 1) : d178888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d178888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17206, d178888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17207 q = 1) (hb : d159762 q = 1) : d178889 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17207, d178889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17207, d178889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128406 q = 1) (hb : d159762 q = 1) : d178957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128406, d178957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40404 q ha hb
    | true =>
      simp only [d128406, d178957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40412 q ha hb
  have h7 (q : Pattern) (ha : d17355 q = 1) (hb : d159762 q = 1) : d178970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17355, d178970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40386 q ha hb
    | true =>
      simp only [d17355, d178970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40387 q ha hb
  have h8 (q : Pattern) (ha : d128407 q = 1) (hb : d159762 q = 1) : d178971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128407, d178971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128407, d178971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128408 q = 1) (hb : d159762 q = 1) : d178972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d178972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128408, d178972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128409 q = 1) (hb : d159762 q = 1) : d178973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d178973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128409, d178973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128413 q = 1) (hb : d159762 q = 1) : d178977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d178977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128413, d178977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40413 q ha hb
  have h12 (q : Pattern) (ha : d17364 q = 1) (hb : d159762 q = 1) : d178979 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17364, d178979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17364, d178979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40388 q ha hb
  have h13 (q : Pattern) (ha : d128414 q = 1) (hb : d159762 q = 1) : d178980 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d178980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128414, d178980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128415 q = 1) (hb : d159762 q = 1) : d178981 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d178981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128415, d178981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128416 q = 1) (hb : d159762 q = 1) : d178982 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d178982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128416, d178982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128417 q = 1) (hb : d159762 q = 1) : d178983 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d178983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128417, d178983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128423 q = 1) (hb : d159762 q = 1) : d179037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d179037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128423, d179037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40424 q ha hb
  have h18 (q : Pattern) (ha : d17501 q = 1) (hb : d159762 q = 1) : d179048 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17501, d179048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17501, d179048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40393 q ha hb
  have h19 (q : Pattern) (ha : d128424 q = 1) (hb : d159762 q = 1) : d179049 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d179049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128424, d179049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128425 q = 1) (hb : d159762 q = 1) : d179050 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d179050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128425, d179050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128426 q = 1) (hb : d159762 q = 1) : d179051 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d179051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128426, d179051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128427 q = 1) (hb : d159762 q = 1) : d179052 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d179052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128427, d179052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128428 q = 1) (hb : d159762 q = 1) : d179053 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d179053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128428, d179053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40426 (p : Pattern) (ha : d128434 p = 1) (hb : d159762 p = 1) : d179059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d159762 q = 1) : d179054 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d179054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d179054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40425 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d159762 q = 1) : d179055 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d179055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d179055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d159762 q = 1) : d179056 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d179056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d179056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d159762 q = 1) : d179057 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d179057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d179057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d159762 q = 1) : d179058 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d179058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d179058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d159762 q = 1) : d179059 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d179059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d179059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40427 (p : Pattern) (ha : d128440 p = 1) (hb : d159762 p = 1) : d179065 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d159762 q = 1) : d178296 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d178296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40173 q ha hb
    | true =>
      simp only [d128269, d178296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40215 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d159762 q = 1) : d178448 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d178448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d178448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40261 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d159762 q = 1) : d178449 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d178449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d178449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d159762 q = 1) : d178615 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d178615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d178615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40316 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d159762 q = 1) : d178616 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d178616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d178616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d159762 q = 1) : d178617 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d178617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d178617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d159762 q = 1) : d178839 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d178839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d178839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40371 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d159762 q = 1) : d178840 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d178840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d178840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d159762 q = 1) : d178841 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d178841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d178841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d159762 q = 1) : d178842 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d178842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d178842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d159762 q = 1) : d179060 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d179060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d179060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40426 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d159762 q = 1) : d179061 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d179061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d179061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d159762 q = 1) : d179062 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d179062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d179062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d159762 q = 1) : d179063 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d179063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d179063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d159762 q = 1) : d179064 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d179064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d179064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d159762 q = 1) : d179065 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d179065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d179065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro40428 (p : Pattern) (ha : d128446 p = 1) (hb : d159762 p = 1) : d179071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d159762 q = 1) : d179066 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d179066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40427 q ha hb
    | true =>
      simp only [d128441, d179066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d159762 q = 1) : d179067 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d179067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d179067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d159762 q = 1) : d179068 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d179068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d179068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d159762 q = 1) : d179069 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d179069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d179069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d159762 q = 1) : d179070 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d179070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d179070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d159762 q = 1) : d179071 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d179071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d179071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40429 (p : Pattern) (ha : d128452 p = 1) (hb : d159762 p = 1) : d179077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d159762 q = 1) : d179072 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d179072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40428 q ha hb
    | true =>
      simp only [d128447, d179072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d159762 q = 1) : d179073 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d179073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d179073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d159762 q = 1) : d179074 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d179074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d179074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d159762 q = 1) : d179075 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d179075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d179075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d159762 q = 1) : d179076 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d179076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d179076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d159762 q = 1) : d179077 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d179077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d179077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40430 (p : Pattern) (ha : d128458 p = 1) (hb : d159762 p = 1) : d179083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d159762 q = 1) : d179078 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d179078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40429 q ha hb
    | true =>
      simp only [d128453, d179078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d159762 q = 1) : d179079 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d179079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d179079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d159762 q = 1) : d179080 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d179080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d179080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d159762 q = 1) : d179081 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d179081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d179081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d159762 q = 1) : d179082 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d179082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d179082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128458 q = 1) (hb : d159762 q = 1) : d179083 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d179083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d179083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40431 (p : Pattern) (ha : d128464 p = 1) (hb : d159762 p = 1) : d179089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d159762 q = 1) : d179084 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d179084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40430 q ha hb
    | true =>
      simp only [d128459, d179084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d159762 q = 1) : d179085 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d179085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d179085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d159762 q = 1) : d179086 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d179086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d179086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d159762 q = 1) : d179087 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d179087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d179087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d159762 q = 1) : d179088 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d179088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d179088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d159762 q = 1) : d179089 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d179089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d179089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40432 (p : Pattern) (ha : d128470 p = 1) (hb : d159762 p = 1) : d179095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d159762 q = 1) : d179090 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d179090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40431 q ha hb
    | true =>
      simp only [d128465, d179090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d159762 q = 1) : d179091 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d179091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d179091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d159762 q = 1) : d179092 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d179092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d179092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d159762 q = 1) : d179093 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d179093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d179093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d159762 q = 1) : d179094 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d179094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d179094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d159762 q = 1) : d179095 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d179095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d179095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40433 (p : Pattern) (ha : d128476 p = 1) (hb : d159762 p = 1) : d179101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d159762 q = 1) : d179096 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d179096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40432 q ha hb
    | true =>
      simp only [d128471, d179096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d159762 q = 1) : d179097 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d179097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d179097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d159762 q = 1) : d179098 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d179098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d179098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d159762 q = 1) : d179099 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d179099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d179099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d159762 q = 1) : d179100 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d179100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d179100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d159762 q = 1) : d179101 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d179101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d179101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40434 (p : Pattern) (ha : d128482 p = 1) (hb : d159762 p = 1) : d179107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d159762 q = 1) : d179102 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d179102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40433 q ha hb
    | true =>
      simp only [d128477, d179102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d159762 q = 1) : d179103 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d179103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d179103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d159762 q = 1) : d179104 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d179104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d179104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d159762 q = 1) : d179105 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d179105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d179105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d159762 q = 1) : d179106 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d179106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d179106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d159762 q = 1) : d179107 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d179107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d179107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40435 (p : Pattern) (ha : d51880 p = 1) (hb : d159797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
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
  have h6 (q : Pattern) (ha : d51880 q = 1) (hb : d159796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d51880 q = 1) (hb : d159797 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40436 (p : Pattern) (ha : d144109 p = 1) (hb : d159803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144104 q = 1) (hb : d159798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144104, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40435 q ha hb
    | true =>
      simp only [d144104, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144105 q = 1) (hb : d159799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144105, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144105, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144106 q = 1) (hb : d159800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144106, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144106, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144107 q = 1) (hb : d159801 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144107, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144107, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144108 q = 1) (hb : d159802 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144108, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144108, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144109 q = 1) (hb : d159803 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144109, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144109, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40437 (p : Pattern) (ha : d144115 p = 1) (hb : d159809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144112 q = 1) (hb : d159806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144113 q = 1) (hb : d159807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144114 q = 1) (hb : d159808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144114, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144114, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144115 q = 1) (hb : d159809 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144115, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144115, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40438 (p : Pattern) (ha : d144121 p = 1) (hb : d159815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144117 q = 1) (hb : d159811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144118 q = 1) (hb : d159812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144118, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144118, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144119 q = 1) (hb : d159813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144119, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144119, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144120 q = 1) (hb : d159814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144120, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144120, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144121 q = 1) (hb : d159815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144121, d159815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144121, d159815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40439 (p : Pattern) (ha : d144122 p = 1) (hb : d159816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144112 q = 1) (hb : d159806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144113 q = 1) (hb : d159807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144114 q = 1) (hb : d159808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144114, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144114, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144122 q = 1) (hb : d159816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144122, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144122, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40440 (p : Pattern) (ha : d144128 p = 1) (hb : d159822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144117 q = 1) (hb : d159811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144118 q = 1) (hb : d159812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144118, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144118, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144119 q = 1) (hb : d159813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144119, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144119, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144120 q = 1) (hb : d159814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144120, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144120, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144124 q = 1) (hb : d159818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144125 q = 1) (hb : d159819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144125, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144125, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144126 q = 1) (hb : d159820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144126, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144126, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144127 q = 1) (hb : d159821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144127, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144127, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144128 q = 1) (hb : d159822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144128, d159822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144128, d159822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40441 (p : Pattern) (ha : d144133 p = 1) (hb : d159827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144124 q = 1) (hb : d159818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144125 q = 1) (hb : d159819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144125, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144125, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144126 q = 1) (hb : d159820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144126, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144126, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144127 q = 1) (hb : d159821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144127, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144127, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144133 q = 1) (hb : d159827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144133, d159827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144133, d159827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40442 (p : Pattern) (ha : d51921 p = 1) (hb : d159834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
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
  have h8 (q : Pattern) (ha : d51921 q = 1) (hb : d159833 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d51921 q = 1) (hb : d159834 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40443 (p : Pattern) (ha : d144144 p = 1) (hb : d159840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144139 q = 1) (hb : d159835 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144139, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40442 q ha hb
    | true =>
      simp only [d144139, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144140 q = 1) (hb : d159836 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144140, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144140, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144141 q = 1) (hb : d159837 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144141, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144141, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144142 q = 1) (hb : d159838 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144142, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144142, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144143 q = 1) (hb : d159839 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144143, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144143, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144144 q = 1) (hb : d159840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144144, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144144, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40444 (p : Pattern) (ha : d144150 p = 1) (hb : d159846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144145 q = 1) (hb : d159841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144145, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40443 q ha hb
    | true =>
      simp only [d144145, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144146 q = 1) (hb : d159842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144146, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144146, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144147 q = 1) (hb : d159843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144147, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144147, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144148 q = 1) (hb : d159844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144148, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144148, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144149 q = 1) (hb : d159845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144149, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144149, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144150 q = 1) (hb : d159846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144150, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144150, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40445 (p : Pattern) (ha : d144156 p = 1) (hb : d159852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144151 q = 1) (hb : d159847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40444 q ha hb
    | true =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144152 q = 1) (hb : d159848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144152, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144152, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144153 q = 1) (hb : d159849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144153, d159849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144153, d159849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144154 q = 1) (hb : d159850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144154, d159850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144154, d159850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144155 q = 1) (hb : d159851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144155, d159851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144155, d159851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144156 q = 1) (hb : d159852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144156, d159852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144156, d159852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40446 (p : Pattern) (ha : d144162 p = 1) (hb : d159858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144129 q = 1) (hb : d159823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144129, d159823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40438 q ha hb
    | true =>
      simp only [d144129, d159823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40440 q ha hb
  have h2 (q : Pattern) (ha : d144130 q = 1) (hb : d159824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144130, d159824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144130, d159824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144131 q = 1) (hb : d159825 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144131, d159825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144131, d159825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144132 q = 1) (hb : d159826 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144132, d159826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144132, d159826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144134 q = 1) (hb : d159828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144134, d159828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144134, d159828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40441 q ha hb
  have h6 (q : Pattern) (ha : d144135 q = 1) (hb : d159829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144135, d159829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144135, d159829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144136 q = 1) (hb : d159830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144136, d159830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144136, d159830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d144137 q = 1) (hb : d159831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144137, d159831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144137, d159831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144138 q = 1) (hb : d159832 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144138, d159832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144138, d159832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144157 q = 1) (hb : d159853 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144157, d159853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144157, d159853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40445 q ha hb
  have h11 (q : Pattern) (ha : d144158 q = 1) (hb : d159854 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144158, d159854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d144158, d159854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144159 q = 1) (hb : d159855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144159, d159855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144159, d159855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d144160 q = 1) (hb : d159856 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d144160, d159856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d144160, d159856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d144161 q = 1) (hb : d159857 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d144161, d159857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d144161, d159857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d144162 q = 1) (hb : d159858 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d144162, d159858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144162, d159858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40447 (p : Pattern) (ha : d144172 p = 1) (hb : d159868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144168 q = 1) (hb : d159864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144169 q = 1) (hb : d159865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144170 q = 1) (hb : d159866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144171 q = 1) (hb : d159867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144172 q = 1) (hb : d159868 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144172, d159868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144172, d159868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40448 (p : Pattern) (ha : d144179 p = 1) (hb : d159875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144168 q = 1) (hb : d159864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144169 q = 1) (hb : d159865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144170 q = 1) (hb : d159866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144171 q = 1) (hb : d159867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144175 q = 1) (hb : d159871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144175, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144175, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144176 q = 1) (hb : d159872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144176, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144176, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144177 q = 1) (hb : d159873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144177, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144177, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144178 q = 1) (hb : d159874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144178, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144178, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144179 q = 1) (hb : d159875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144179, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144179, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40449 (p : Pattern) (ha : d144230 p = 1) (hb : d159928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144168 q = 1) (hb : d159864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144169 q = 1) (hb : d159865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144170 q = 1) (hb : d159866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144171 q = 1) (hb : d159867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144230 q = 1) (hb : d159928 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144230, d159928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144230, d159928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40450 (p : Pattern) (ha : d144184 p = 1) (hb : d159880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144112 q = 1) (hb : d159806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144113 q = 1) (hb : d159807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144183 q = 1) (hb : d159879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144183, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144183, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144184 q = 1) (hb : d159880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144184, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144184, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40451 (p : Pattern) (ha : d144191 p = 1) (hb : d159887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144112 q = 1) (hb : d159806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144189 q = 1) (hb : d159885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144189, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144189, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144190 q = 1) (hb : d159886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144190, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144190, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144191 q = 1) (hb : d159887 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144191, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144191, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40452 (p : Pattern) (ha : d138 p = 1) (hb : d101014 p = 1) : d29114 p = 1 := by
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
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d21 q = 1) : d21 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d74174 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d74174, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d74174, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d74175 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d74175, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d74175, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h12 (q : Pattern) (ha : d138 q = 1) (hb : d101014 q = 1) : d29114 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d101014, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138, d101014, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro40453 (p : Pattern) (ha : d112928 p = 1) (hb : d159892 p = 1) : d179109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d101015 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d101015, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40452 q ha hb
    | true =>
      simp only [d139, d101015, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d101017 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d101017, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d101017, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d141 q = 1) (hb : d112927 q = 1) : d29117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d112927, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d141, d112927, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142 q = 1) (hb : d112928 q = 1) : d29118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d112928, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d142, d112928, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d112928 q = 1) (hb : d159891 q = 1) : d179108 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d159891, d179108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d159891, d179108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112928 q = 1) (hb : d159892 q = 1) : d179109 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d159892, d179109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159892, d179109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40454 (p : Pattern) (ha : d159898 p = 1) (hb : d177189 p = 1) : d179115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159893 q = 1) (hb : d177184 q = 1) : d179110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d159893, d177184, d179110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40453 q hb ha
    | true =>
      simp only [d159893, d177184, d179110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40435 q hb ha
  have h2 (q : Pattern) (ha : d159894 q = 1) (hb : d177185 q = 1) : d179111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d159894, d177185, d179111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159894, d177185, d179111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159895 q = 1) (hb : d177186 q = 1) : d179112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d159895, d177186, d179112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159895, d177186, d179112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144104 q = 1) (hb : d159798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144104, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40435 q ha hb
    | true =>
      simp only [d144104, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144105 q = 1) (hb : d159799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144105, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144105, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144106 q = 1) (hb : d159800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144106, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144106, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159896 q = 1) (hb : d177187 q = 1) : d179113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d159896, d177187, d179113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159896, d177187, d179113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144107 q = 1) (hb : d159801 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144107, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144107, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d159897 q = 1) (hb : d177188 q = 1) : d179114 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d159897, d177188, d179114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d159897, d177188, d179114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d159898 q = 1) (hb : d177189 q = 1) : d179115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d159898, d177189, d179115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d159898, d177189, d179115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40455 (p : Pattern) (ha : d159904 p = 1) (hb : d177195 p = 1) : d179121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159901 q = 1) (hb : d177192 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159902 q = 1) (hb : d177193 q = 1) : d179119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d159903 q = 1) (hb : d177194 q = 1) : d179120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d159903, d177194, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159903, d177194, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d159904 q = 1) (hb : d177195 q = 1) : d179121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d159904, d177195, d179121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159904, d177195, d179121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40456 (p : Pattern) (ha : d159910 p = 1) (hb : d177201 p = 1) : d179127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144185 q = 1) (hb : d159881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144185, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40450 q ha hb
    | true =>
      simp only [d144185, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144186 q = 1) (hb : d159882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144186, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144186, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144187 q = 1) (hb : d159883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144187, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144187, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144188 q = 1) (hb : d159884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144188, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144188, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144192 q = 1) (hb : d159888 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144192, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40451 q ha hb
    | true =>
      simp only [d144192, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144193 q = 1) (hb : d159889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144193, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144193, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144194 q = 1) (hb : d159890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144194, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144194, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159905 q = 1) (hb : d177196 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q ha hb
    | true =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d159906 q = 1) (hb : d177197 q = 1) : d179123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159906, d177197, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159906, d177197, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144117 q = 1) (hb : d159811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d159907 q = 1) (hb : d177198 q = 1) : d179124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159907, d177198, d179124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d159907, d177198, d179124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d159908 q = 1) (hb : d177199 q = 1) : d179125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159908, d177199, d179125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d159908, d177199, d179125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d159909 q = 1) (hb : d177200 q = 1) : d179126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159909, d177200, d179126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d159909, d177200, d179126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d159910 q = 1) (hb : d177201 q = 1) : d179127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159910, d177201, d179127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159910, d177201, d179127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40457 (p : Pattern) (ha : d144213 p = 1) (hb : d159911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144112 q = 1) (hb : d159806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144113 q = 1) (hb : d159807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144113, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144183 q = 1) (hb : d159879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144183, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144183, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144213 q = 1) (hb : d159911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144213, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144213, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40458 (p : Pattern) (ha : d144218 p = 1) (hb : d159916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144112 q = 1) (hb : d159806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144112, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144189 q = 1) (hb : d159885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144189, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144189, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144190 q = 1) (hb : d159886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144190, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144190, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144218 q = 1) (hb : d159916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144218, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144218, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40459 (p : Pattern) (ha : d159920 p = 1) (hb : d177202 p = 1) : d179128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159901 q = 1) (hb : d177192 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159902 q = 1) (hb : d177193 q = 1) : d179119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d159903 q = 1) (hb : d177194 q = 1) : d179120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d159903, d177194, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159903, d177194, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d159920 q = 1) (hb : d177202 q = 1) : d179128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d159920, d177202, d179128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d159920, d177202, d179128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40460 (p : Pattern) (ha : d159926 p = 1) (hb : d177208 p = 1) : d179134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144185 q = 1) (hb : d159881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144185, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40450 q ha hb
    | true =>
      simp only [d144185, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144186 q = 1) (hb : d159882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144186, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144186, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144187 q = 1) (hb : d159883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144187, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144187, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144188 q = 1) (hb : d159884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144188, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144188, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144192 q = 1) (hb : d159888 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144192, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40451 q ha hb
    | true =>
      simp only [d144192, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144193 q = 1) (hb : d159889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144193, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144193, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d144194 q = 1) (hb : d159890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144194, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144194, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159905 q = 1) (hb : d177196 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q ha hb
    | true =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d144116 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d159906 q = 1) (hb : d177197 q = 1) : d179123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159906, d177197, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159906, d177197, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d144117 q = 1) (hb : d159811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144117, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d159907 q = 1) (hb : d177198 q = 1) : d179124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159907, d177198, d179124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d159907, d177198, d179124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d159908 q = 1) (hb : d177199 q = 1) : d179125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159908, d177199, d179125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d159908, d177199, d179125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d159909 q = 1) (hb : d177200 q = 1) : d179126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159909, d177200, d179126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d159909, d177200, d179126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d144214 q = 1) (hb : d159912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144214, d159912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40457 q ha hb
    | true =>
      simp only [d144214, d159912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d144215 q = 1) (hb : d159913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144215, d159913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144215, d159913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d144216 q = 1) (hb : d159914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144216, d159914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d144216, d159914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d144217 q = 1) (hb : d159915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144217, d159915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144217, d159915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d144219 q = 1) (hb : d159917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144219, d159917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40458 q ha hb
    | true =>
      simp only [d144219, d159917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d144220 q = 1) (hb : d159918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144220, d159918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144220, d159918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d144221 q = 1) (hb : d159919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144221, d159919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d144221, d159919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d159921 q = 1) (hb : d177203 q = 1) : d179129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40459 q ha hb
    | true =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d159922 q = 1) (hb : d177204 q = 1) : d179130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159922, d177204, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d159922, d177204, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d144124 q = 1) (hb : d159818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d159923 q = 1) (hb : d177205 q = 1) : d179131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159923, d177205, d179131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d159923, d177205, d179131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d159924 q = 1) (hb : d177206 q = 1) : d179132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159924, d177206, d179132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d159924, d177206, d179132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d159925 q = 1) (hb : d177207 q = 1) : d179133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159925, d177207, d179133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d159925, d177207, d179133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d159926 q = 1) (hb : d177208 q = 1) : d179134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159926, d177208, d179134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d159926, d177208, d179134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro40461 (p : Pattern) (ha : d159935 p = 1) (hb : d177215 p = 1) : d179139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159921 q = 1) (hb : d177203 q = 1) : d179129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40459 q ha hb
    | true =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159922 q = 1) (hb : d177204 q = 1) : d179130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159922, d177204, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159922, d177204, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144124 q = 1) (hb : d159818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144124, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159923 q = 1) (hb : d177205 q = 1) : d179131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159923, d177205, d179131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159923, d177205, d179131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d159933 q = 1) (hb : d177213 q = 1) : d179132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159933, d177213, d179132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159933, d177213, d179132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159934 q = 1) (hb : d177214 q = 1) : d179133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159934, d177214, d179133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159934, d177214, d179133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159935 q = 1) (hb : d177215 q = 1) : d179139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159935, d177215, d179139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159935, d177215, d179139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40462 (p : Pattern) (ha : d113010 p = 1) (hb : d159942 p = 1) : d179146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d226 q = 1) (hb : d113007 q = 1) : d29395 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d113007, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d226, d113007, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40452 q ha hb
  have h3 (q : Pattern) (ha : d139 q = 1) (hb : d101015 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d101015, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40452 q ha hb
    | true =>
      simp only [d139, d101015, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d227 q = 1) (hb : d113008 q = 1) : d29396 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d113008, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d227, d113008, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140 q = 1) (hb : d101017 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d101017, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140, d101017, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d228 q = 1) (hb : d113009 q = 1) : d29397 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d113009, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d228, d113009, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d229 q = 1) (hb : d113010 q = 1) : d29398 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d113010, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d229, d113010, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d113010 q = 1) (hb : d159941 q = 1) : d179145 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d159941, d179145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d159941, d179145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d113010 q = 1) (hb : d159942 q = 1) : d179146 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d159942, d179146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159942, d179146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40463 (p : Pattern) (ha : d159948 p = 1) (hb : d177226 p = 1) : d179152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159943 q = 1) (hb : d177221 q = 1) : d179147 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d159943, d177221, d179147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40462 q hb ha
    | true =>
      simp only [d159943, d177221, d179147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40442 q hb ha
  have h2 (q : Pattern) (ha : d159944 q = 1) (hb : d177222 q = 1) : d179148 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d159944, d177222, d179148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159944, d177222, d179148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159945 q = 1) (hb : d177223 q = 1) : d179149 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d159945, d177223, d179149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159945, d177223, d179149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144139 q = 1) (hb : d159835 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144139, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40442 q ha hb
    | true =>
      simp only [d144139, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144140 q = 1) (hb : d159836 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144140, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144140, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144141 q = 1) (hb : d159837 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144141, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144141, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159946 q = 1) (hb : d177224 q = 1) : d179150 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d159946, d177224, d179150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159946, d177224, d179150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144142 q = 1) (hb : d159838 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144142, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144142, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d159947 q = 1) (hb : d177225 q = 1) : d179151 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d159947, d177225, d179151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d159947, d177225, d179151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d159948 q = 1) (hb : d177226 q = 1) : d179152 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d159948, d177226, d179152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d159948, d177226, d179152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40464 (p : Pattern) (ha : d159954 p = 1) (hb : d177232 p = 1) : d179158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159949 q = 1) (hb : d177227 q = 1) : d179153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159949, d177227, d179153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40463 q ha hb
    | true =>
      simp only [d159949, d177227, d179153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159950 q = 1) (hb : d177228 q = 1) : d179154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159950, d177228, d179154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159950, d177228, d179154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144145 q = 1) (hb : d159841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144145, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40443 q ha hb
    | true =>
      simp only [d144145, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144146 q = 1) (hb : d159842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144146, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144146, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159951 q = 1) (hb : d177229 q = 1) : d179155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d159951, d177229, d179155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159951, d177229, d179155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159952 q = 1) (hb : d177230 q = 1) : d179156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d159952, d177230, d179156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159952, d177230, d179156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d159953 q = 1) (hb : d177231 q = 1) : d179157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d159953, d177231, d179157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159953, d177231, d179157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d159954 q = 1) (hb : d177232 q = 1) : d179158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d159954, d177232, d179158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d159954, d177232, d179158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40465 (p : Pattern) (ha : d159960 p = 1) (hb : d177238 p = 1) : d179164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159955 q = 1) (hb : d177233 q = 1) : d179159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159955, d177233, d179159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40464 q ha hb
    | true =>
      simp only [d159955, d177233, d179159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40444 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144151 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159956 q = 1) (hb : d177234 q = 1) : d179160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159956, d177234, d179160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159956, d177234, d179160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144151 q = 1) (hb : d159847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40444 q ha hb
    | true =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144152 q = 1) (hb : d159848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144152, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144152, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159957 q = 1) (hb : d177235 q = 1) : d179161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159957, d177235, d179161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159957, d177235, d179161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d159958 q = 1) (hb : d177236 q = 1) : d179162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159958, d177236, d179162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159958, d177236, d179162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159959 q = 1) (hb : d177237 q = 1) : d179163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159959, d177237, d179163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159959, d177237, d179163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159960 q = 1) (hb : d177238 q = 1) : d179164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159960, d177238, d179164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159960, d177238, d179164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40466 (p : Pattern) (ha : d159966 p = 1) (hb : d177244 p = 1) : d179170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144173 q = 1) (hb : d159869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144173, d159869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144173, d159869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40447 q ha hb
  have h2 (q : Pattern) (ha : d144174 q = 1) (hb : d159870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144174, d159870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d144174, d159870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d144180 q = 1) (hb : d159876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144180, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40447 q ha hb
    | true =>
      simp only [d144180, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40448 q ha hb
  have h4 (q : Pattern) (ha : d144181 q = 1) (hb : d159877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d144181, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144181, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144182 q = 1) (hb : d159878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d144182, d159878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144182, d159878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159927 q = 1) (hb : d177209 q = 1) : d179135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159927, d177209, d179135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40456 q ha hb
    | true =>
      simp only [d159927, d177209, d179135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40460 q ha hb
  have h7 (q : Pattern) (ha : d144231 q = 1) (hb : d159929 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144231, d159929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40449 q ha hb
    | true =>
      simp only [d144231, d159929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159930 q = 1) (hb : d177210 q = 1) : d179136 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159930, d177210, d179136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159930, d177210, d179136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d159931 q = 1) (hb : d177211 q = 1) : d179137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d159931, d177211, d179137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159931, d177211, d179137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d159932 q = 1) (hb : d177212 q = 1) : d179138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d159932, d177212, d179138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d159932, d177212, d179138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d159936 q = 1) (hb : d177216 q = 1) : d179140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159936, d177216, d179140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159936, d177216, d179140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40461 q ha hb
  have h12 (q : Pattern) (ha : d159937 q = 1) (hb : d177217 q = 1) : d179141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159937, d177217, d179141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d159937, d177217, d179141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d159938 q = 1) (hb : d177218 q = 1) : d179142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d159938, d177218, d179142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d159938, d177218, d179142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d159939 q = 1) (hb : d177219 q = 1) : d179143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d159939, d177219, d179143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d159939, d177219, d179143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d159940 q = 1) (hb : d177220 q = 1) : d179144 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d159940, d177220, d179144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d159940, d177220, d179144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d159961 q = 1) (hb : d177239 q = 1) : d179165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159961, d177239, d179165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159961, d177239, d179165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40465 q ha hb
  have h17 (q : Pattern) (ha : d159962 q = 1) (hb : d177240 q = 1) : d179166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159962, d177240, d179166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d159962, d177240, d179166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d159963 q = 1) (hb : d177241 q = 1) : d179167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d159963, d177241, d179167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d159963, d177241, d179167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d159964 q = 1) (hb : d177242 q = 1) : d179168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d159964, d177242, d179168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d159964, d177242, d179168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d159965 q = 1) (hb : d177243 q = 1) : d179169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d159965, d177243, d179169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d159965, d177243, d179169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d159966 q = 1) (hb : d177244 q = 1) : d179170 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d159966, d177244, d179170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d159966, d177244, d179170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro40467 (p : Pattern) (ha : d159972 p = 1) (hb : d177250 p = 1) : d179176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144163 q = 1) (hb : d159859 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d144163, d159859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144163, d159859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40446 q ha hb
  have h2 (q : Pattern) (ha : d144164 q = 1) (hb : d159860 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d144164, d159860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144164, d159860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144165 q = 1) (hb : d159861 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d144165, d159861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144165, d159861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144166 q = 1) (hb : d159862 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d144166, d159862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144166, d159862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144167 q = 1) (hb : d159863 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d144167, d159863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144167, d159863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159967 q = 1) (hb : d177245 q = 1) : d179171 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d159967, d177245, d179171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159967, d177245, d179171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40466 q ha hb
  have h7 (q : Pattern) (ha : d159968 q = 1) (hb : d177246 q = 1) : d179172 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d159968, d177246, d179172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159968, d177246, d179172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159969 q = 1) (hb : d177247 q = 1) : d179173 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d159969, d177247, d179173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159969, d177247, d179173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159970 q = 1) (hb : d177248 q = 1) : d179174 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d159970, d177248, d179174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159970, d177248, d179174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159971 q = 1) (hb : d177249 q = 1) : d179175 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d159971, d177249, d179175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159971, d177249, d179175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d159972 q = 1) (hb : d177250 q = 1) : d179176 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d159972, d177250, d179176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d159972, d177250, d179176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40468 (p : Pattern) (ha : d144353 p = 1) (hb : d160055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144175 q = 1) (hb : d159871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144175, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144175, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144176 q = 1) (hb : d159872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144176, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144176, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144177 q = 1) (hb : d159873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144177, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144177, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144178 q = 1) (hb : d159874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144178, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144178, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144353 q = 1) (hb : d160055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144353, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144353, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40469 (p : Pattern) (ha : d144388 p = 1) (hb : d160092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144151 q = 1) (hb : d159847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40444 q ha hb
    | true =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144384 q = 1) (hb : d160088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144384, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144384, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144385 q = 1) (hb : d160089 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144385, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144385, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144386 q = 1) (hb : d160090 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144386, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144386, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144387 q = 1) (hb : d160091 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144387, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144387, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144388 q = 1) (hb : d160092 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144388, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144388, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40470 (p : Pattern) (ha : d159977 p = 1) (hb : d177255 p = 1) : d179181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159905 q = 1) (hb : d177196 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q ha hb
    | true =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q hb ha
  have h2 (q : Pattern) (ha : d159973 q = 1) (hb : d177251 q = 1) : d179177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159973, d177251, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159973, d177251, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159974 q = 1) (hb : d177252 q = 1) : d179178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159974, d177252, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159974, d177252, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159975 q = 1) (hb : d177253 q = 1) : d179179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159975, d177253, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159975, d177253, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159976 q = 1) (hb : d177254 q = 1) : d179180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159976, d177254, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159976, d177254, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159977 q = 1) (hb : d177255 q = 1) : d179181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159977, d177255, d179181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159977, d177255, d179181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40471 (p : Pattern) (ha : d159984 p = 1) (hb : d177262 p = 1) : d179188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159905 q = 1) (hb : d177196 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q ha hb
    | true =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q hb ha
  have h2 (q : Pattern) (ha : d159973 q = 1) (hb : d177251 q = 1) : d179177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159973, d177251, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159973, d177251, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159974 q = 1) (hb : d177252 q = 1) : d179178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159974, d177252, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159974, d177252, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159975 q = 1) (hb : d177253 q = 1) : d179179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159975, d177253, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159975, d177253, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159976 q = 1) (hb : d177254 q = 1) : d179180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159976, d177254, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159976, d177254, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159921 q = 1) (hb : d177203 q = 1) : d179129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40459 q ha hb
    | true =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q hb ha
  have h7 (q : Pattern) (ha : d159980 q = 1) (hb : d177258 q = 1) : d179184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159980, d177258, d179184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159980, d177258, d179184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159981 q = 1) (hb : d177259 q = 1) : d179185 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159981, d177259, d179185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d159981, d177259, d179185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d159982 q = 1) (hb : d177260 q = 1) : d179186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159982, d177260, d179186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159982, d177260, d179186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159983 q = 1) (hb : d177261 q = 1) : d179187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159983, d177261, d179187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159983, d177261, d179187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d159984 q = 1) (hb : d177262 q = 1) : d179188 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159984, d177262, d179188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159984, d177262, d179188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40472 (p : Pattern) (ha : d160046 p = 1) (hb : d177322 p = 1) : d179250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159905 q = 1) (hb : d177196 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q ha hb
    | true =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q hb ha
  have h2 (q : Pattern) (ha : d159973 q = 1) (hb : d177251 q = 1) : d179177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159973, d177251, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159973, d177251, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159974 q = 1) (hb : d177252 q = 1) : d179178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159974, d177252, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159974, d177252, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159975 q = 1) (hb : d177253 q = 1) : d179179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159975, d177253, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159975, d177253, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159976 q = 1) (hb : d177254 q = 1) : d179180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159976, d177254, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159976, d177254, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144168 q = 1) (hb : d159864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144168, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144169 q = 1) (hb : d159865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144169, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144170 q = 1) (hb : d159866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144170, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144171 q = 1) (hb : d159867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144171, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d160046 q = 1) (hb : d177322 q = 1) : d179250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160046, d177322, d179250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160046, d177322, d179250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro40473 (p : Pattern) (ha : d159989 p = 1) (hb : d177267 p = 1) : d179193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159901 q = 1) (hb : d177192 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159902 q = 1) (hb : d177193 q = 1) : d179119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d159988 q = 1) (hb : d177266 q = 1) : d179192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d159988, d177266, d179192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159988, d177266, d179192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159989 q = 1) (hb : d177267 q = 1) : d179193 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d159989, d177267, d179193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159989, d177267, d179193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40474 (p : Pattern) (ha : d159996 p = 1) (hb : d177274 p = 1) : d179200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159901 q = 1) (hb : d177192 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159994 q = 1) (hb : d177272 q = 1) : d179198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d159994, d177272, d179198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159994, d177272, d179198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159995 q = 1) (hb : d177273 q = 1) : d179199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d159995, d177273, d179199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159995, d177273, d179199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d159996 q = 1) (hb : d177274 q = 1) : d179200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d159996, d177274, d179200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159996, d177274, d179200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40475 (p : Pattern) (ha : d160019 p = 1) (hb : d177295 p = 1) : d179121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160016 q = 1) (hb : d177292 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160016, d177292, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160016, d177292, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160017 q = 1) (hb : d177293 q = 1) : d179119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160017, d177293, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160017, d177293, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160018 q = 1) (hb : d177294 q = 1) : d179120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160018, d177294, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160018, d177294, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160019 q = 1) (hb : d177295 q = 1) : d179121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160019, d177295, d179121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160019, d177295, d179121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40476 (p : Pattern) (ha : d132 p = 1) (hb : d69101 p = 1) : d46473 p = 1 := by
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
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d130 q = 1) (hb : d52281 q = 1) : d45587 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d52281, d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130, d52281, d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
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
  have h9 (q : Pattern) (ha : d131 q = 1) (hb : d69100 q = 1) : d46472 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d69100, d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131, d69100, d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d132 q = 1) (hb : d69101 q = 1) : d46473 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d132, d69101, d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d132, d69101, d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40477 (p : Pattern) (ha : d9457 p = 1) (hb : d101082 p = 1) : d179208 p = 1 := by
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
  have h3 (q : Pattern) (ha : d133 q = 1) (hb : d101067 q = 1) : d46477 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d101067, d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40476 q ha hb
    | true =>
      simp only [d133, d101067, d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d134 q = 1) (hb : d101068 q = 1) : d179204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d101068, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d134, d101068, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d315 q = 1) (hb : d101079 q = 1) : d179205 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d101079, d179205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315, d101079, d179205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d135 q = 1) : d135 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d316 q = 1) (hb : d101080 q = 1) : d179206 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d101080, d179206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316, d101080, d179206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d317 q = 1) (hb : d101081 q = 1) : d179207 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d101081, d179207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d317, d101081, d179207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9452 q = 1) (hb : d101067 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9453 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9454 q = 1) (hb : d101069 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d101069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9454, d101069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9455 q = 1) (hb : d101070 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d101070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9455, d101070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9456 q = 1) (hb : d101071 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d101071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9456, d101071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9457 q = 1) (hb : d101082 q = 1) : d179208 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9457, d101082, d179208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9457, d101082, d179208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40478 (p : Pattern) (ha : d113135 p = 1) (hb : d178226 p = 1) : d179214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9458 q = 1) (hb : d101083 q = 1) : d179209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101083, d179209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40477 q ha hb
    | true =>
      simp only [d9458, d101083, d179209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9460 q = 1) (hb : d101085 q = 1) : d179210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101085, d179210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9460, d101085, d179210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16073 q = 1) (hb : d113134 q = 1) : d179211 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d113134, d179211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16073, d113134, d179211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16074 q = 1) (hb : d113135 q = 1) : d179212 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d113135, d179212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16074, d113135, d179212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d113135 q = 1) (hb : d178225 q = 1) : d179213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178225, d179213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178225, d179213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113135 q = 1) (hb : d178226 q = 1) : d179214 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178226, d179214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178226, d179214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40479 (p : Pattern) (ha : d177283 p = 1) (hb : d178232 p = 1) : d179220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177278 q = 1) (hb : d178227 q = 1) : d179215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177278, d178227, d179215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40478 q ha hb
    | true =>
      simp only [d177278, d178227, d179215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40453 q ha hb
  have h2 (q : Pattern) (ha : d177279 q = 1) (hb : d178228 q = 1) : d179216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177279, d178228, d179216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177279, d178228, d179216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177280 q = 1) (hb : d178229 q = 1) : d179217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177280, d178229, d179217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177280, d178229, d179217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159893 q = 1) (hb : d177184 q = 1) : d179110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d159893, d177184, d179110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40453 q hb ha
    | true =>
      simp only [d159893, d177184, d179110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40435 q hb ha
  have h5 (q : Pattern) (ha : d159894 q = 1) (hb : d177185 q = 1) : d179111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d159894, d177185, d179111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159894, d177185, d179111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159895 q = 1) (hb : d177186 q = 1) : d179112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d159895, d177186, d179112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159895, d177186, d179112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177281 q = 1) (hb : d178230 q = 1) : d179218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177281, d178230, d179218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177281, d178230, d179218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144104 q = 1) (hb : d159798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144104, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40435 q ha hb
    | true =>
      simp only [d144104, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144105 q = 1) (hb : d159799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144105, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144105, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144106 q = 1) (hb : d159800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144106, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144106, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d159896 q = 1) (hb : d177187 q = 1) : d179113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d159896, d177187, d179113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159896, d177187, d179113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d177282 q = 1) (hb : d178231 q = 1) : d179219 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177282, d178231, d179219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177282, d178231, d179219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d177283 q = 1) (hb : d178232 q = 1) : d179220 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177283, d178232, d179220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d177283, d178232, d179220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40480 (p : Pattern) (ha : d177289 p = 1) (hb : d178238 p = 1) : d179226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177284 q = 1) (hb : d178233 q = 1) : d179221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177284, d178233, d179221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40479 q ha hb
    | true =>
      simp only [d177284, d178233, d179221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177285 q = 1) (hb : d178234 q = 1) : d179222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177285, d178234, d179222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177285, d178234, d179222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177286 q = 1) (hb : d178235 q = 1) : d179223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177286, d178235, d179223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177286, d178235, d179223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177287 q = 1) (hb : d178236 q = 1) : d179224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177287, d178236, d179224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177287, d178236, d179224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177288 q = 1) (hb : d178237 q = 1) : d179225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177288, d178237, d179225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177288, d178237, d179225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177289 q = 1) (hb : d178238 q = 1) : d179226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177289, d178238, d179226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177289, d178238, d179226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40481 (p : Pattern) (ha : d177301 p = 1) (hb : d178244 p = 1) : d179232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159990 q = 1) (hb : d177268 q = 1) : d179194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159990, d177268, d179194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40473 q ha hb
    | true =>
      simp only [d159990, d177268, d179194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40450 q hb ha
  have h2 (q : Pattern) (ha : d159991 q = 1) (hb : d177269 q = 1) : d179195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159991, d177269, d179195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159991, d177269, d179195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159992 q = 1) (hb : d177270 q = 1) : d179196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159992, d177270, d179196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159992, d177270, d179196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159993 q = 1) (hb : d177271 q = 1) : d179197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159993, d177271, d179197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159993, d177271, d179197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159997 q = 1) (hb : d177275 q = 1) : d179201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159997, d177275, d179201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40474 q ha hb
    | true =>
      simp only [d159997, d177275, d179201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40451 q hb ha
  have h6 (q : Pattern) (ha : d159998 q = 1) (hb : d177276 q = 1) : d179202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159998, d177276, d179202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159998, d177276, d179202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159999 q = 1) (hb : d177277 q = 1) : d179203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159999, d177277, d179203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159999, d177277, d179203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d177290 q = 1) (hb : d178239 q = 1) : d179227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177290, d178239, d179227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40480 q ha hb
    | true =>
      simp only [d177290, d178239, d179227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177196 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177291 q = 1) (hb : d178240 q = 1) : d179228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177291, d178240, d179228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177291, d178240, d179228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d160020 q = 1) (hb : d177296 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160020, d177296, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40475 q ha hb
    | true =>
      simp only [d160020, d177296, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d160021 q = 1) (hb : d177297 q = 1) : d179123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160021, d177297, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d160021, d177297, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d177298 q = 1) (hb : d178241 q = 1) : d179229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177298, d178241, d179229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177298, d178241, d179229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d177299 q = 1) (hb : d178242 q = 1) : d179230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177299, d178242, d179230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d177299, d178242, d179230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177300 q = 1) (hb : d178243 q = 1) : d179231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177300, d178243, d179231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177300, d178243, d179231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177301 q = 1) (hb : d178244 q = 1) : d179232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177301, d178244, d179232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177301, d178244, d179232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40482 (p : Pattern) (ha : d160026 p = 1) (hb : d177302 p = 1) : d179233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159901 q = 1) (hb : d177192 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159902 q = 1) (hb : d177193 q = 1) : d179119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159902, d177193, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d159988 q = 1) (hb : d177266 q = 1) : d179192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d159988, d177266, d179192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159988, d177266, d179192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d160026 q = 1) (hb : d177302 q = 1) : d179233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160026, d177302, d179233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d160026, d177302, d179233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40483 (p : Pattern) (ha : d160031 p = 1) (hb : d177307 p = 1) : d179238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144110 q = 1) (hb : d159804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40436 q ha hb
    | true =>
      simp only [d144110, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144111 q = 1) (hb : d159805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144111, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159901 q = 1) (hb : d177192 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159901, d177192, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159994 q = 1) (hb : d177272 q = 1) : d179198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d159994, d177272, d179198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159994, d177272, d179198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159995 q = 1) (hb : d177273 q = 1) : d179199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d159995, d177273, d179199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159995, d177273, d179199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d160031 q = 1) (hb : d177307 q = 1) : d179238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160031, d177307, d179238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d160031, d177307, d179238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40484 (p : Pattern) (ha : d160038 p = 1) (hb : d177314 p = 1) : d179128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160016 q = 1) (hb : d177292 q = 1) : d179118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160016, d177292, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160016, d177292, d179118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160017 q = 1) (hb : d177293 q = 1) : d179119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160017, d177293, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160017, d177293, d179119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160018 q = 1) (hb : d177294 q = 1) : d179120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160018, d177294, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160018, d177294, d179120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160038 q = 1) (hb : d177314 q = 1) : d179128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160038, d177314, d179128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160038, d177314, d179128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40485 (p : Pattern) (ha : d177311 p = 1) (hb : d178245 p = 1) : d179242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177284 q = 1) (hb : d178233 q = 1) : d179221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177284, d178233, d179221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40479 q ha hb
    | true =>
      simp only [d177284, d178233, d179221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177285 q = 1) (hb : d178234 q = 1) : d179222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177285, d178234, d179222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177285, d178234, d179222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159899 q = 1) (hb : d177190 q = 1) : d179116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40454 q ha hb
    | true =>
      simp only [d159899, d177190, d179116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159900 q = 1) (hb : d177191 q = 1) : d179117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159900, d177191, d179117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177286 q = 1) (hb : d178235 q = 1) : d179223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177286, d178235, d179223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177286, d178235, d179223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177287 q = 1) (hb : d178236 q = 1) : d179224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177287, d178236, d179224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177287, d178236, d179224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177288 q = 1) (hb : d178237 q = 1) : d179225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177288, d178237, d179225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177288, d178237, d179225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177311 q = 1) (hb : d178245 q = 1) : d179242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177311, d178245, d179242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177311, d178245, d179242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40486 (p : Pattern) (ha : d177320 p = 1) (hb : d178251 p = 1) : d179248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159990 q = 1) (hb : d177268 q = 1) : d179194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159990, d177268, d179194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40473 q ha hb
    | true =>
      simp only [d159990, d177268, d179194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40450 q hb ha
  have h2 (q : Pattern) (ha : d159991 q = 1) (hb : d177269 q = 1) : d179195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159991, d177269, d179195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159991, d177269, d179195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159992 q = 1) (hb : d177270 q = 1) : d179196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159992, d177270, d179196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159992, d177270, d179196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159993 q = 1) (hb : d177271 q = 1) : d179197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159993, d177271, d179197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159993, d177271, d179197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159997 q = 1) (hb : d177275 q = 1) : d179201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159997, d177275, d179201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40474 q ha hb
    | true =>
      simp only [d159997, d177275, d179201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40451 q hb ha
  have h6 (q : Pattern) (ha : d159998 q = 1) (hb : d177276 q = 1) : d179202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159998, d177276, d179202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159998, d177276, d179202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159999 q = 1) (hb : d177277 q = 1) : d179203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159999, d177277, d179203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159999, d177277, d179203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d177290 q = 1) (hb : d178239 q = 1) : d179227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177290, d178239, d179227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40480 q ha hb
    | true =>
      simp only [d177290, d178239, d179227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177196 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177291 q = 1) (hb : d178240 q = 1) : d179228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177291, d178240, d179228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177291, d178240, d179228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d160020 q = 1) (hb : d177296 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160020, d177296, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40475 q ha hb
    | true =>
      simp only [d160020, d177296, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d160021 q = 1) (hb : d177297 q = 1) : d179123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160021, d177297, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d160021, d177297, d179123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d177298 q = 1) (hb : d178241 q = 1) : d179229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177298, d178241, d179229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177298, d178241, d179229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d177299 q = 1) (hb : d178242 q = 1) : d179230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177299, d178242, d179230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d177299, d178242, d179230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177300 q = 1) (hb : d178243 q = 1) : d179231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177300, d178243, d179231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d177300, d178243, d179231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d160027 q = 1) (hb : d177303 q = 1) : d179234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160027, d177303, d179234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40482 q ha hb
    | true =>
      simp only [d160027, d177303, d179234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40457 q hb ha
  have h17 (q : Pattern) (ha : d160028 q = 1) (hb : d177304 q = 1) : d179235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160028, d177304, d179235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160028, d177304, d179235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d160029 q = 1) (hb : d177305 q = 1) : d179236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160029, d177305, d179236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d160029, d177305, d179236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d160030 q = 1) (hb : d177306 q = 1) : d179237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160030, d177306, d179237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160030, d177306, d179237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d160032 q = 1) (hb : d177308 q = 1) : d179239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160032, d177308, d179239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40483 q ha hb
    | true =>
      simp only [d160032, d177308, d179239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40458 q hb ha
  have h21 (q : Pattern) (ha : d160033 q = 1) (hb : d177309 q = 1) : d179240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160033, d177309, d179240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160033, d177309, d179240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d160034 q = 1) (hb : d177310 q = 1) : d179241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160034, d177310, d179241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d160034, d177310, d179241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d177312 q = 1) (hb : d178246 q = 1) : d179243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177312, d178246, d179243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40485 q ha hb
    | true =>
      simp only [d177312, d178246, d179243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40459 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d177203 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d177313 q = 1) (hb : d178247 q = 1) : d179244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177313, d178247, d179244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d177313, d178247, d179244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d160039 q = 1) (hb : d177315 q = 1) : d179129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160039, d177315, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40484 q ha hb
    | true =>
      simp only [d160039, d177315, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d160040 q = 1) (hb : d177316 q = 1) : d179130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160040, d177316, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d160040, d177316, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d177317 q = 1) (hb : d178248 q = 1) : d179245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177317, d178248, d179245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d177317, d178248, d179245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d177318 q = 1) (hb : d178249 q = 1) : d179246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177318, d178249, d179246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d177318, d178249, d179246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d177319 q = 1) (hb : d178250 q = 1) : d179247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177319, d178250, d179247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d177319, d178250, d179247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d177320 q = 1) (hb : d178251 q = 1) : d179248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177320, d178251, d179248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d177320, d178251, d179248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro40487 (p : Pattern) (ha : d177329 p = 1) (hb : d178258 p = 1) : d179257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177312 q = 1) (hb : d178246 q = 1) : d179243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177312, d178246, d179243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40485 q ha hb
    | true =>
      simp only [d177312, d178246, d179243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40459 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177313 q = 1) (hb : d178247 q = 1) : d179244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177313, d178247, d179244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177313, d178247, d179244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d160039 q = 1) (hb : d177315 q = 1) : d179129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160039, d177315, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40484 q ha hb
    | true =>
      simp only [d160039, d177315, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160040 q = 1) (hb : d177316 q = 1) : d179130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160040, d177316, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160040, d177316, d179130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d177317 q = 1) (hb : d178248 q = 1) : d179245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177317, d178248, d179245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177317, d178248, d179245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d177327 q = 1) (hb : d178256 q = 1) : d179255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177327, d178256, d179255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177327, d178256, d179255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177328 q = 1) (hb : d178257 q = 1) : d179256 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177328, d178257, d179256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177328, d178257, d179256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177329 q = 1) (hb : d178258 q = 1) : d179257 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177329, d178258, d179257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177329, d178258, d179257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40488 (p : Pattern) (ha : d160080 p = 1) (hb : d177352 p = 1) : d179158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159949 q = 1) (hb : d177227 q = 1) : d179153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159949, d177227, d179153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40463 q ha hb
    | true =>
      simp only [d159949, d177227, d179153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d159950 q = 1) (hb : d177228 q = 1) : d179154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159950, d177228, d179154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159950, d177228, d179154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160077 q = 1) (hb : d177349 q = 1) : d179155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160077, d177349, d179155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160077, d177349, d179155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160078 q = 1) (hb : d177350 q = 1) : d179156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160078, d177350, d179156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160078, d177350, d179156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160079 q = 1) (hb : d177351 q = 1) : d179157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160079, d177351, d179157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160079, d177351, d179157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160080 q = 1) (hb : d177352 q = 1) : d179158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160080, d177352, d179158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160080, d177352, d179158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40489 (p : Pattern) (ha : d113217 p = 1) (hb : d178265 p = 1) : d179268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16156 q = 1) (hb : d113214 q = 1) : d179263 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d113214, d179263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16156, d113214, d179263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40477 q ha hb
  have h3 (q : Pattern) (ha : d9458 q = 1) (hb : d101083 q = 1) : d179209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101083, d179209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40477 q ha hb
    | true =>
      simp only [d9458, d101083, d179209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16157 q = 1) (hb : d113215 q = 1) : d179264 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d113215, d179264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16157, d113215, d179264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9460 q = 1) (hb : d101085 q = 1) : d179210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101085, d179210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9460, d101085, d179210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16158 q = 1) (hb : d113216 q = 1) : d179265 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d113216, d179265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16158, d113216, d179265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16159 q = 1) (hb : d113217 q = 1) : d179266 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d113217, d179266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16159, d113217, d179266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d113217 q = 1) (hb : d178264 q = 1) : d179267 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178264, d179267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178264, d179267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d113217 q = 1) (hb : d178265 q = 1) : d179268 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178265, d179268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178265, d179268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40490 (p : Pattern) (ha : d177340 p = 1) (hb : d178271 p = 1) : d179274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177335 q = 1) (hb : d178266 q = 1) : d179269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177335, d178266, d179269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40489 q ha hb
    | true =>
      simp only [d177335, d178266, d179269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40462 q ha hb
  have h2 (q : Pattern) (ha : d177336 q = 1) (hb : d178267 q = 1) : d179270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177336, d178267, d179270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177336, d178267, d179270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177337 q = 1) (hb : d178268 q = 1) : d179271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177337, d178268, d179271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177337, d178268, d179271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159943 q = 1) (hb : d177221 q = 1) : d179147 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d159943, d177221, d179147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40462 q hb ha
    | true =>
      simp only [d159943, d177221, d179147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40442 q hb ha
  have h5 (q : Pattern) (ha : d159944 q = 1) (hb : d177222 q = 1) : d179148 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d159944, d177222, d179148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159944, d177222, d179148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159945 q = 1) (hb : d177223 q = 1) : d179149 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d159945, d177223, d179149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159945, d177223, d179149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177338 q = 1) (hb : d178269 q = 1) : d179272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177338, d178269, d179272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177338, d178269, d179272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d144139 q = 1) (hb : d159835 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144139, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40442 q ha hb
    | true =>
      simp only [d144139, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144140 q = 1) (hb : d159836 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144140, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144140, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144141 q = 1) (hb : d159837 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144141, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144141, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d159946 q = 1) (hb : d177224 q = 1) : d179150 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d159946, d177224, d179150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d159946, d177224, d179150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d177339 q = 1) (hb : d178270 q = 1) : d179273 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177339, d178270, d179273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177339, d178270, d179273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d177340 q = 1) (hb : d178271 q = 1) : d179274 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177340, d178271, d179274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d177340, d178271, d179274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40491 (p : Pattern) (ha : d177346 p = 1) (hb : d178277 p = 1) : d179280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177341 q = 1) (hb : d178272 q = 1) : d179275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177341, d178272, d179275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40490 q ha hb
    | true =>
      simp only [d177341, d178272, d179275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177342 q = 1) (hb : d178273 q = 1) : d179276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177342, d178273, d179276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177342, d178273, d179276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159949 q = 1) (hb : d177227 q = 1) : d179153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d159949, d177227, d179153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40463 q ha hb
    | true =>
      simp only [d159949, d177227, d179153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d159950 q = 1) (hb : d177228 q = 1) : d179154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d159950, d177228, d179154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159950, d177228, d179154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177343 q = 1) (hb : d178274 q = 1) : d179277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177343, d178274, d179277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177343, d178274, d179277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177344 q = 1) (hb : d178275 q = 1) : d179278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177344, d178275, d179278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177344, d178275, d179278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177345 q = 1) (hb : d178276 q = 1) : d179279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177345, d178276, d179279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177345, d178276, d179279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177346 q = 1) (hb : d178277 q = 1) : d179280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177346, d178277, d179280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177346, d178277, d179280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40492 (p : Pattern) (ha : d177358 p = 1) (hb : d178283 p = 1) : d179286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177347 q = 1) (hb : d178278 q = 1) : d179281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177347, d178278, d179281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40491 q ha hb
    | true =>
      simp only [d177347, d178278, d179281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40464 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177233 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177348 q = 1) (hb : d178279 q = 1) : d179282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177348, d178279, d179282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177348, d178279, d179282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d160081 q = 1) (hb : d177353 q = 1) : d179159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160081, d177353, d179159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40488 q ha hb
    | true =>
      simp only [d160081, d177353, d179159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160082 q = 1) (hb : d177354 q = 1) : d179160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160082, d177354, d179160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160082, d177354, d179160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d177355 q = 1) (hb : d178280 q = 1) : d179283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177355, d178280, d179283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177355, d178280, d179283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d177356 q = 1) (hb : d178281 q = 1) : d179284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177356, d178281, d179284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177356, d178281, d179284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177357 q = 1) (hb : d178282 q = 1) : d179285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177357, d178282, d179285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177357, d178282, d179285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177358 q = 1) (hb : d178283 q = 1) : d179286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177358, d178283, d179286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177358, d178283, d179286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40493 (p : Pattern) (ha : d177364 p = 1) (hb : d178289 p = 1) : d179292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159978 q = 1) (hb : d177256 q = 1) : d179182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159978, d177256, d179182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159978, d177256, d179182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40470 q ha hb
  have h2 (q : Pattern) (ha : d159979 q = 1) (hb : d177257 q = 1) : d179183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159979, d177257, d179183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159979, d177257, d179183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d159985 q = 1) (hb : d177263 q = 1) : d179189 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159985, d177263, d179189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40470 q ha hb
    | true =>
      simp only [d159985, d177263, d179189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40471 q ha hb
  have h4 (q : Pattern) (ha : d159986 q = 1) (hb : d177264 q = 1) : d179190 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159986, d177264, d179190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159986, d177264, d179190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d159987 q = 1) (hb : d177265 q = 1) : d179191 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d159987, d177265, d179191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159987, d177265, d179191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177321 q = 1) (hb : d178252 q = 1) : d179249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177321, d178252, d179249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40481 q ha hb
    | true =>
      simp only [d177321, d178252, d179249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40486 q ha hb
  have h7 (q : Pattern) (ha : d160047 q = 1) (hb : d177323 q = 1) : d179251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d160047, d177323, d179251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40472 q ha hb
    | true =>
      simp only [d160047, d177323, d179251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40448 q hb ha
  have h8 (q : Pattern) (ha : d177324 q = 1) (hb : d178253 q = 1) : d179252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177324, d178253, d179252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177324, d178253, d179252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d177325 q = 1) (hb : d178254 q = 1) : d179253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177325, d178254, d179253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177325, d178254, d179253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177326 q = 1) (hb : d178255 q = 1) : d179254 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177326, d178255, d179254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d177326, d178255, d179254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177330 q = 1) (hb : d178259 q = 1) : d179258 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177330, d178259, d179258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177330, d178259, d179258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40487 q ha hb
  have h12 (q : Pattern) (ha : d144354 q = 1) (hb : d160056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144354, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144354, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40468 q ha hb
  have h13 (q : Pattern) (ha : d177331 q = 1) (hb : d178260 q = 1) : d179259 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177331, d178260, d179259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177331, d178260, d179259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177332 q = 1) (hb : d178261 q = 1) : d179260 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177332, d178261, d179260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177332, d178261, d179260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d177333 q = 1) (hb : d178262 q = 1) : d179261 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177333, d178262, d179261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d177333, d178262, d179261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d177334 q = 1) (hb : d178263 q = 1) : d179262 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177334, d178263, d179262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177334, d178263, d179262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177359 q = 1) (hb : d178284 q = 1) : d179287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177359, d178284, d179287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177359, d178284, d179287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40492 q ha hb
  have h18 (q : Pattern) (ha : d144389 q = 1) (hb : d160093 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144389, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144389, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40469 q ha hb
  have h19 (q : Pattern) (ha : d177360 q = 1) (hb : d178285 q = 1) : d179288 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177360, d178285, d179288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177360, d178285, d179288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d177361 q = 1) (hb : d178286 q = 1) : d179289 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177361, d178286, d179289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d177361, d178286, d179289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d177362 q = 1) (hb : d178287 q = 1) : d179290 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177362, d178287, d179290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d177362, d178287, d179290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d177363 q = 1) (hb : d178288 q = 1) : d179291 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177363, d178288, d179291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d177363, d178288, d179291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d177364 q = 1) (hb : d178289 q = 1) : d179292 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177364, d178289, d179292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177364, d178289, d179292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40494 (p : Pattern) (ha : d177370 p = 1) (hb : d178295 p = 1) : d179298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177365 q = 1) (hb : d178290 q = 1) : d179293 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177365, d178290, d179293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177365, d178290, d179293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40493 q ha hb
  have h2 (q : Pattern) (ha : d177366 q = 1) (hb : d178291 q = 1) : d179294 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177366, d178291, d179294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177366, d178291, d179294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177367 q = 1) (hb : d178292 q = 1) : d179295 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177367, d178292, d179295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177367, d178292, d179295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177368 q = 1) (hb : d178293 q = 1) : d179296 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177368, d178293, d179296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177368, d178293, d179296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177369 q = 1) (hb : d178294 q = 1) : d179297 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177369, d178294, d179297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177369, d178294, d179297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177370 q = 1) (hb : d178295 q = 1) : d179298 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177370, d178295, d179298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177370, d178295, d179298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40495 (p : Pattern) (ha : d52431 p = 1) (hb : d160107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d52431 q = 1) (hb : d160106 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52431 q = 1) (hb : d160107 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40496 (p : Pattern) (ha : d144415 p = 1) (hb : d160121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144405 q = 1) (hb : d160111 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144405, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40495 q ha hb
    | true =>
      simp only [d144405, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144406 q = 1) (hb : d160112 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144406, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144406, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144407 q = 1) (hb : d160113 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144407, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144407, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144409 q = 1) (hb : d160115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144409, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144409, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144414 q = 1) (hb : d160120 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144414, d160120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144414, d160120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144415 q = 1) (hb : d160121 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144415, d160121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144415, d160121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40497 (p : Pattern) (ha : d144425 p = 1) (hb : d160131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144422 q = 1) (hb : d160128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144423 q = 1) (hb : d160129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144424 q = 1) (hb : d160130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144424, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144424, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144425 q = 1) (hb : d160131 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144425, d160131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144425, d160131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40498 (p : Pattern) (ha : d144435 p = 1) (hb : d160141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144422 q = 1) (hb : d160128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144423 q = 1) (hb : d160129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144424 q = 1) (hb : d160130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144424, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144424, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144435 q = 1) (hb : d160141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144435, d160141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144435, d160141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40499 (p : Pattern) (ha : d144519 p = 1) (hb : d160227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144508 q = 1) (hb : d160216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144508, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40497 q ha hb
    | true =>
      simp only [d144508, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144509 q = 1) (hb : d160217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144509, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144509, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144510 q = 1) (hb : d160218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144510, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144510, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144511 q = 1) (hb : d160219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144511, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144511, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144512 q = 1) (hb : d160220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144512, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144512, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144514 q = 1) (hb : d160222 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144514, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40498 q ha hb
    | true =>
      simp only [d144514, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144515 q = 1) (hb : d160223 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144515, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144515, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144516 q = 1) (hb : d160224 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144516, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144516, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144517 q = 1) (hb : d160225 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144517, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144517, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144518 q = 1) (hb : d160226 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144518, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144518, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d144519 q = 1) (hb : d160227 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144519, d160227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144519, d160227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
end NetHack.Soko22Hazard87
