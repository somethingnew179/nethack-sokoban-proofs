import NetHack.Soko22Hazard87.AndIntroBlocks0231
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro58000 (p : Pattern) (ha : d237473 p = 1) (hb : d238369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29881 q = 1) (hb : d237464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29881, d237464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29881, d237464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57957 q ha hb
  have h2 (q : Pattern) (ha : d29558 q = 1) (hb : d237230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d237230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57957 q ha hb
    | true =>
      simp only [d29558, d237230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29882 q = 1) (hb : d237465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29882, d237465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29882, d237465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29559 q = 1) (hb : d237231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d237231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29559, d237231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29883 q = 1) (hb : d237466 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29883, d237466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29883, d237466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29884 q = 1) (hb : d237467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29884, d237467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29884, d237467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d237468 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237468, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237468, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57958 q ha hb
  have h8 (q : Pattern) (ha : d237235 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57958 q ha hb
    | true =>
      simp only [d237235, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237469 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237469, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237469, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237236 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237236, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237470 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237470, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237470, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237471 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237471, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237471, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237472 q = 1) (hb : d238363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237472, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237472, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237449 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237449, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237449, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57955 q ha hb
  have h15 (q : Pattern) (ha : d237221 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237221, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57955 q ha hb
    | true =>
      simp only [d237221, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237450 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237450, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237450, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237222 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237222, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237222, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237451 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237451, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237451, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237452 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237452, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237452, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237458 q = 1) (hb : d238368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237458, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237458, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237473 q = 1) (hb : d238369 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237473, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237473, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58001 (p : Pattern) (ha : d237483 p = 1) (hb : d238374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237468 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237468, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237468, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57958 q ha hb
  have h2 (q : Pattern) (ha : d237235 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57958 q ha hb
    | true =>
      simp only [d237235, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237469 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237469, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237469, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237236 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237236, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237470 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237470, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237470, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237471 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237471, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237471, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237477 q = 1) (hb : d238368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237477, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237477, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237483 q = 1) (hb : d238374 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237483, d238374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237483, d238374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro58002 (p : Pattern) (ha : d237489 p = 1) (hb : d238380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237455 q = 1) (hb : d238365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237455, d238365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57997 q hb ha
    | true =>
      simp only [d237455, d238365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57998 q ha hb
  have h2 (q : Pattern) (ha : d237456 q = 1) (hb : d238366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237456, d238366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237456, d238366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237457 q = 1) (hb : d238367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237457, d238367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237457, d238367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237460 q = 1) (hb : d238370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237460, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57998 q ha hb
    | true =>
      simp only [d237460, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57999 q ha hb
  have h5 (q : Pattern) (ha : d237461 q = 1) (hb : d238371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237461, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237461, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237462 q = 1) (hb : d238372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237462, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237462, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237463 q = 1) (hb : d238373 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237463, d238373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237463, d238373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237474 q = 1) (hb : d238370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237474, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57998 q ha hb
    | true =>
      simp only [d237474, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58000 q ha hb
  have h9 (q : Pattern) (ha : d237475 q = 1) (hb : d238371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237475, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237475, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237476 q = 1) (hb : d238372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237476, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237476, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237484 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58000 q ha hb
    | true =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58001 q ha hb
  have h12 (q : Pattern) (ha : d237485 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237486 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237487 q = 1) (hb : d238378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237487, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237487, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237488 q = 1) (hb : d238379 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237488, d238379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237488, d238379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237489 q = 1) (hb : d238380 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237489, d238380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237489, d238380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro58003 (p : Pattern) (ha : d237494 p = 1) (hb : d238385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237474 q = 1) (hb : d238370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237474, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57998 q ha hb
    | true =>
      simp only [d237474, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58000 q ha hb
  have h2 (q : Pattern) (ha : d237475 q = 1) (hb : d238371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237475, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237475, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237476 q = 1) (hb : d238372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237476, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237476, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237484 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58000 q ha hb
    | true =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58001 q ha hb
  have h5 (q : Pattern) (ha : d237485 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237486 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237487 q = 1) (hb : d238378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237487, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237487, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237492 q = 1) (hb : d238383 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237492, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237492, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237493 q = 1) (hb : d238384 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237493, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237493, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237494 q = 1) (hb : d238385 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237494, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237494, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro58004 (p : Pattern) (ha : d237500 p = 1) (hb : d238391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237490 q = 1) (hb : d238381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237490, d238381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58002 q ha hb
    | true =>
      simp only [d237490, d238381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237491 q = 1) (hb : d238382 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237491, d238382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237491, d238382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237495 q = 1) (hb : d238386 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237495, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58003 q ha hb
    | true =>
      simp only [d237495, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237496 q = 1) (hb : d238387 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237496, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237496, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237497 q = 1) (hb : d238388 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237497, d238388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237497, d238388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237498 q = 1) (hb : d238389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237498, d238389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237498, d238389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237499 q = 1) (hb : d238390 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237499, d238390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237499, d238390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237500 q = 1) (hb : d238391 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237500, d238391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237500, d238391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58005 (p : Pattern) (ha : d237502 p = 1) (hb : d238393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237484 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58000 q ha hb
    | true =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58001 q ha hb
  have h2 (q : Pattern) (ha : d237485 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237486 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237492 q = 1) (hb : d238383 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237492, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237492, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237501 q = 1) (hb : d238392 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237501, d238392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237501, d238392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237502 q = 1) (hb : d238393 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237502, d238393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237502, d238393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58006 (p : Pattern) (ha : d237508 p = 1) (hb : d238399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237495 q = 1) (hb : d238386 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237495, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58003 q ha hb
    | true =>
      simp only [d237495, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237496 q = 1) (hb : d238387 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237496, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237496, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237503 q = 1) (hb : d238394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237503, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58005 q ha hb
    | true =>
      simp only [d237503, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237504 q = 1) (hb : d238395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237504, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237504, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237505 q = 1) (hb : d238396 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237505, d238396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237505, d238396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237506 q = 1) (hb : d238397 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237506, d238397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237506, d238397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237507 q = 1) (hb : d238398 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237507, d238398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237507, d238398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237508 q = 1) (hb : d238399 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237508, d238399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237508, d238399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58007 (p : Pattern) (ha : d237521 p = 1) (hb : d238369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29881 q = 1) (hb : d237464 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29881, d237464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29881, d237464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57957 q ha hb
  have h2 (q : Pattern) (ha : d29558 q = 1) (hb : d237230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d237230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57957 q ha hb
    | true =>
      simp only [d29558, d237230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29882 q = 1) (hb : d237465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29882, d237465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29882, d237465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29559 q = 1) (hb : d237231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d237231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29559, d237231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29883 q = 1) (hb : d237466 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29883, d237466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29883, d237466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29884 q = 1) (hb : d237467 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29884, d237467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29884, d237467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d237468 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237468, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237468, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57958 q ha hb
  have h8 (q : Pattern) (ha : d237235 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57958 q ha hb
    | true =>
      simp only [d237235, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237469 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237469, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237469, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237236 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237236, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237470 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237470, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237470, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237471 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237471, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237471, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237472 q = 1) (hb : d238363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237472, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237472, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237516 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237516, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237516, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57979 q ha hb
  have h15 (q : Pattern) (ha : d237346 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237346, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57979 q ha hb
    | true =>
      simp only [d237346, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237517 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237517, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237517, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237347 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237347, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237347, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237518 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237518, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237518, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237519 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237519, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237519, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237520 q = 1) (hb : d238368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237520, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237520, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237521 q = 1) (hb : d238369 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237521, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237521, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58008 (p : Pattern) (ha : d237527 p = 1) (hb : d238374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237522 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237522, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237522, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57981 q ha hb
  have h2 (q : Pattern) (ha : d237353 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237353, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57981 q ha hb
    | true =>
      simp only [d237353, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237523 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237523, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237523, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237354 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237354, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237354, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237524 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237524, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237524, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237525 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237525, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237525, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237526 q = 1) (hb : d238368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237526, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237526, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237527 q = 1) (hb : d238374 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237527, d238374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237527, d238374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58009 (p : Pattern) (ha : d237533 p = 1) (hb : d238385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237474 q = 1) (hb : d238370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237474, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57998 q ha hb
    | true =>
      simp only [d237474, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58000 q ha hb
  have h2 (q : Pattern) (ha : d237475 q = 1) (hb : d238371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237475, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237475, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237476 q = 1) (hb : d238372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237476, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237476, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237484 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58000 q ha hb
    | true =>
      simp only [d237484, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58001 q ha hb
  have h5 (q : Pattern) (ha : d237485 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237486 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237487 q = 1) (hb : d238378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237487, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237487, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237528 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237528, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58007 q ha hb
    | true =>
      simp only [d237528, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58008 q ha hb
  have h9 (q : Pattern) (ha : d237529 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237529, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237529, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237530 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237530, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237530, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237531 q = 1) (hb : d238383 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237531, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237531, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237532 q = 1) (hb : d238384 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237532, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237532, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237533 q = 1) (hb : d238385 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237533, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237533, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro58010 (p : Pattern) (ha : d237539 p = 1) (hb : d238405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237534 q = 1) (hb : d238386 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237534, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58009 q ha hb
    | true =>
      simp only [d237534, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237535 q = 1) (hb : d238387 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237535, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237535, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237536 q = 1) (hb : d238402 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237536, d238402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237536, d238402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237537 q = 1) (hb : d238403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237537, d238403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237537, d238403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237538 q = 1) (hb : d238404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237538, d238404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237538, d238404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237539 q = 1) (hb : d238405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237539, d238405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237539, d238405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58011 (p : Pattern) (ha : d237545 p = 1) (hb : d238411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237509 q = 1) (hb : d238400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237509, d238400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58004 q ha hb
    | true =>
      simp only [d237509, d238400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58006 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237515 q = 1) (hb : d238401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237515, d238401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237515, d238401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237540 q = 1) (hb : d238406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237540, d238406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58010 q ha hb
    | true =>
      simp only [d237540, d238406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237541 q = 1) (hb : d238407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237541, d238407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237541, d238407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237542 q = 1) (hb : d238408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237542, d238408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237542, d238408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237543 q = 1) (hb : d238409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237543, d238409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237543, d238409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237544 q = 1) (hb : d238410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237544, d238410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237544, d238410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237545 q = 1) (hb : d238411 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237545, d238411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237545, d238411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro58012 (p : Pattern) (ha : d237513 p = 1) (hb : d238416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237503 q = 1) (hb : d238394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237503, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58005 q ha hb
    | true =>
      simp only [d237503, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237504 q = 1) (hb : d238395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237504, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237504, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237510 q = 1) (hb : d238413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237510, d238413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237510, d238413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237511 q = 1) (hb : d238414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237511, d238414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237511, d238414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237512 q = 1) (hb : d238415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237512, d238415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237512, d238415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237513 q = 1) (hb : d238416 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237513, d238416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237513, d238416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58013 (p : Pattern) (ha : d237552 p = 1) (hb : d238422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237547 q = 1) (hb : d238417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237547, d238417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58012 q ha hb
    | true =>
      simp only [d237547, d238417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237548 q = 1) (hb : d238418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237548, d238418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237548, d238418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237549 q = 1) (hb : d238419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237549, d238419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237549, d238419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237550 q = 1) (hb : d238420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237550, d238420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237550, d238420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237551 q = 1) (hb : d238421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237551, d238421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237551, d238421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237552 q = 1) (hb : d238422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237552, d238422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237552, d238422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58014 (p : Pattern) (ha : d237558 p = 1) (hb : d238428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237282 q = 1) (hb : d238257 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237282, d238257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237282, d238257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57965 q ha hb
  have h2 (q : Pattern) (ha : d237283 q = 1) (hb : d238258 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237283, d238258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237283, d238258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237292 q = 1) (hb : d238267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237292, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57965 q ha hb
    | true =>
      simp only [d237292, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57968 q ha hb
  have h4 (q : Pattern) (ha : d237293 q = 1) (hb : d238268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237293, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237293, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237294 q = 1) (hb : d238269 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237294, d238269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237294, d238269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237398 q = 1) (hb : d238332 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237398, d238332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57985 q ha hb
    | true =>
      simp only [d237398, d238332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57992 q ha hb
  have h7 (q : Pattern) (ha : d237411 q = 1) (hb : d238345 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237411, d238345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57993 q ha hb
    | true =>
      simp only [d237411, d238345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57994 q ha hb
  have h8 (q : Pattern) (ha : d237412 q = 1) (hb : d238346 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237412, d238346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237412, d238346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237413 q = 1) (hb : d238347 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237413, d238347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237413, d238347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d237414 q = 1) (hb : d238348 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237414, d238348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237414, d238348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237418 q = 1) (hb : d238352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237418, d238352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237418, d238352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57995 q ha hb
  have h12 (q : Pattern) (ha : d237420 q = 1) (hb : d238354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237420, d238354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237420, d238354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57996 q ha hb
  have h13 (q : Pattern) (ha : d237421 q = 1) (hb : d238355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237421, d238355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237421, d238355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237422 q = 1) (hb : d238356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237422, d238356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237422, d238356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237423 q = 1) (hb : d238357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237423, d238357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237423, d238357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237424 q = 1) (hb : d238358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237424, d238358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237424, d238358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237546 q = 1) (hb : d238412 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237546, d238412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237546, d238412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58011 q ha hb
  have h18 (q : Pattern) (ha : d237553 q = 1) (hb : d238423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237553, d238423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237553, d238423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58013 q ha hb
  have h19 (q : Pattern) (ha : d237554 q = 1) (hb : d238424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237554, d238424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237554, d238424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237555 q = 1) (hb : d238425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237555, d238425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237555, d238425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237556 q = 1) (hb : d238426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237556, d238426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d237556, d238426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d237557 q = 1) (hb : d238427 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237557, d238427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237557, d238427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237558 q = 1) (hb : d238428 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237558, d238428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237558, d238428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro58015 (p : Pattern) (ha : d237564 p = 1) (hb : d238434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237559 q = 1) (hb : d238429 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237559, d238429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237559, d238429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58014 q ha hb
  have h2 (q : Pattern) (ha : d237560 q = 1) (hb : d238430 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237560, d238430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237560, d238430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237561 q = 1) (hb : d238431 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237561, d238431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237561, d238431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237562 q = 1) (hb : d238432 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237562, d238432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237562, d238432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237563 q = 1) (hb : d238433 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237563, d238433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237563, d238433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237564 q = 1) (hb : d238434 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237564, d238434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237564, d238434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58016 (p : Pattern) (ha : d30087 p = 1) (hb : d237579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30079 q = 1) (hb : d237571 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, d237571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, d237571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30080 q = 1) (hb : d237572 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, d237572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30080, d237572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30081 q = 1) (hb : d237573 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, d237573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30081, d237573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30084 q = 1) (hb : d237576 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d237576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, d237576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30085 q = 1) (hb : d237577 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d237577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30085, d237577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30086 q = 1) (hb : d237578 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d237578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30086, d237578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30087 q = 1) (hb : d237579 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30087, d237579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30087, d237579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58017 (p : Pattern) (ha : d30097 p = 1) (hb : d237589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30084 q = 1) (hb : d237576 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d237576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, d237576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30085 q = 1) (hb : d237577 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d237577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30085, d237577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30086 q = 1) (hb : d237578 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d237578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30086, d237578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30092 q = 1) (hb : d237584 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30093 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30094 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30095 q = 1) (hb : d237587 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30095, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30096 q = 1) (hb : d237588 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30096, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30097 q = 1) (hb : d237589 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30097, d237589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30097, d237589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro58018 (p : Pattern) (ha : d237598 p = 1) (hb : d238441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30092 q = 1) (hb : d237584 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30093 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30094 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30095 q = 1) (hb : d237587 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30095, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30096 q = 1) (hb : d237588 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30096, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30103 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d237596 q = 1) (hb : d238439 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237596, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237596, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d237597 q = 1) (hb : d238440 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237597, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237597, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237598 q = 1) (hb : d238441 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237598, d238441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d237598, d238441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro58019 (p : Pattern) (ha : d237604 p = 1) (hb : d238447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30088 q = 1) (hb : d237580 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58016 q ha hb
    | true =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30089 q = 1) (hb : d237581 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30090 q = 1) (hb : d237582 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, d237582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, d237582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30091 q = 1) (hb : d237583 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, d237583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30091, d237583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30098 q = 1) (hb : d237590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
    | true =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30099 q = 1) (hb : d237591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30100 q = 1) (hb : d237592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d237592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d237592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30101 q = 1) (hb : d237593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d237593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30101, d237593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30102 q = 1) (hb : d237594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, d237594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30102, d237594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237599 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
    | true =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237600 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237601 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237601, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237601, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237602 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237602, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237602, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237603 q = 1) (hb : d238446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237603, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d237603, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237604 q = 1) (hb : d238447 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237604, d238447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237604, d238447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58020 (p : Pattern) (ha : d30097 p = 1) (hb : d237607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30084 q = 1) (hb : d237576 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d237576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30084, d237576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30085 q = 1) (hb : d237577 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d237577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30085, d237577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30086 q = 1) (hb : d237578 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d237578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30086, d237578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30092 q = 1) (hb : d237584 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30093 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30094 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d30095 q = 1) (hb : d237605 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30095, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30096 q = 1) (hb : d237606 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30096, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30097 q = 1) (hb : d237607 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30097, d237607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30097, d237607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro58021 (p : Pattern) (ha : d237612 p = 1) (hb : d238441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30092 q = 1) (hb : d237584 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d30092, d237584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30093 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30093, d237585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30094 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30094, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30095 q = 1) (hb : d237605 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30095, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30096 q = 1) (hb : d237606 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30096, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30103 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d237596 q = 1) (hb : d238439 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237596, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237596, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d237597 q = 1) (hb : d238440 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237597, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237597, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237612 q = 1) (hb : d238441 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237612, d238441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d237612, d238441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58022 (p : Pattern) (ha : d237619 p = 1) (hb : d238449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30098 q = 1) (hb : d237608 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58020 q ha hb
    | true =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30099 q = 1) (hb : d237609 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30100 q = 1) (hb : d237610 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d237610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d237610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30101 q = 1) (hb : d237611 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d237611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30101, d237611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d237613 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
    | true =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237614 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237615 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237615, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237615, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237616 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237616, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237616, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237617 q = 1) (hb : d238446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237617, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237617, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237599 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
    | true =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237600 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237601 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237601, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237601, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237602 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237602, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237602, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237618 q = 1) (hb : d238448 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237618, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237618, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237619 q = 1) (hb : d238449 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237619, d238449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237619, d238449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58023 (p : Pattern) (ha : d237632 p = 1) (hb : d238453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237613 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
    | true =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237614 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237615 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237615, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237615, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237616 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237616, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237616, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237623 q = 1) (hb : d238448 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237623, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237623, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237631 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237632 q = 1) (hb : d238453 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237632, d238453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237632, d238453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro58024 (p : Pattern) (ha : d237639 p = 1) (hb : d238460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237620 q = 1) (hb : d238450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237620, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58019 q ha hb
    | true =>
      simp only [d237620, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58022 q ha hb
  have h2 (q : Pattern) (ha : d237621 q = 1) (hb : d238451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237621, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237621, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237622 q = 1) (hb : d238452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237622, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237622, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237633 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58022 q ha hb
    | true =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58023 q ha hb
  have h5 (q : Pattern) (ha : d237634 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237635 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237636 q = 1) (hb : d238457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237636, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237636, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237637 q = 1) (hb : d238458 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237637, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237637, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237638 q = 1) (hb : d238459 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237638, d238459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237638, d238459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237639 q = 1) (hb : d238460 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237639, d238460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237639, d238460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro58025 (p : Pattern) (ha : d237643 p = 1) (hb : d238464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237633 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58022 q ha hb
    | true =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58023 q ha hb
  have h2 (q : Pattern) (ha : d237634 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237635 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237637 q = 1) (hb : d238458 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237637, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237637, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237642 q = 1) (hb : d238463 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237642, d238463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237642, d238463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237643 q = 1) (hb : d238464 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237643, d238464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237643, d238464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58026 (p : Pattern) (ha : d237649 p = 1) (hb : d238470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237648 q = 1) (hb : d238469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237648, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237648, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237649 q = 1) (hb : d238470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237649, d238470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237649, d238470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58027 (p : Pattern) (ha : d237653 p = 1) (hb : d238474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237652 q = 1) (hb : d238473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237652, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237652, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237653 q = 1) (hb : d238474 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237653, d238474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237653, d238474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58028 (p : Pattern) (ha : d237659 p = 1) (hb : d238480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237654 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58026 q ha hb
    | true =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58027 q ha hb
  have h2 (q : Pattern) (ha : d237655 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237655, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237655, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237656 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237656, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237656, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237657 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237657, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237657, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237658 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237658, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237658, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237659 q = 1) (hb : d238480 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237659, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237659, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58029 (p : Pattern) (ha : d237662 p = 1) (hb : d238483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237648 q = 1) (hb : d238469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237648, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237648, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237662 q = 1) (hb : d238483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237662, d238483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237662, d238483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58030 (p : Pattern) (ha : d237663 p = 1) (hb : d238484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237652 q = 1) (hb : d238473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237652, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237652, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237663 q = 1) (hb : d238484 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237663, d238484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237663, d238484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58031 (p : Pattern) (ha : d237669 p = 1) (hb : d238490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237654 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58026 q ha hb
    | true =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58027 q ha hb
  have h2 (q : Pattern) (ha : d237655 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237655, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237655, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237656 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237656, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237656, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237657 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237657, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237657, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237658 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237658, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237658, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237664 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237664, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58029 q ha hb
    | true =>
      simp only [d237664, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58030 q ha hb
  have h7 (q : Pattern) (ha : d237665 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237665, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237665, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237666 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237666, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237666, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237667 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237667, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237667, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237668 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237668, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237668, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237669 q = 1) (hb : d238490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237669, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237669, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58032 (p : Pattern) (ha : d237674 p = 1) (hb : d238495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237673 q = 1) (hb : d238494 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237673, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237673, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237674 q = 1) (hb : d238495 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237674, d238495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237674, d238495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58033 (p : Pattern) (ha : d237676 p = 1) (hb : d238497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237675 q = 1) (hb : d238496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237675, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237675, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237676 q = 1) (hb : d238497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237676, d238497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237676, d238497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58034 (p : Pattern) (ha : d237683 p = 1) (hb : d238504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237681 q = 1) (hb : d238502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237681, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237681, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237682 q = 1) (hb : d238503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237682, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237682, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237683 q = 1) (hb : d238504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237683, d238504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237683, d238504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58035 (p : Pattern) (ha : d237686 p = 1) (hb : d238507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237684 q = 1) (hb : d238505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237684, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237684, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237685 q = 1) (hb : d238506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237685, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237685, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237686 q = 1) (hb : d238507 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237686, d238507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237686, d238507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58036 (p : Pattern) (ha : d30198 p = 1) (hb : d237690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30079 q = 1) (hb : d237571 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, d237571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, d237571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30080 q = 1) (hb : d237572 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, d237572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30080, d237572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30081 q = 1) (hb : d237573 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, d237573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30081, d237573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30198 q = 1) (hb : d237690 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30198, d237690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30198, d237690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58037 (p : Pattern) (ha : d30204 p = 1) (hb : d237696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30199 q = 1) (hb : d237691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, d237691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58036 q ha hb
    | true =>
      simp only [d30199, d237691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30200 q = 1) (hb : d237692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, d237692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30200, d237692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30201 q = 1) (hb : d237693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30201, d237693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30201, d237693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30202 q = 1) (hb : d237694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30202, d237694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30202, d237694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30088 q = 1) (hb : d237580 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58016 q ha hb
    | true =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30089 q = 1) (hb : d237581 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30090 q = 1) (hb : d237582 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, d237582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, d237582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30091 q = 1) (hb : d237583 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, d237583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30091, d237583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30203 q = 1) (hb : d237695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30203, d237695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30203, d237695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30098 q = 1) (hb : d237590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
    | true =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30099 q = 1) (hb : d237591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30100 q = 1) (hb : d237592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d237592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d237592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30101 q = 1) (hb : d237593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d237593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30101, d237593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30102 q = 1) (hb : d237594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, d237594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30102, d237594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30204 q = 1) (hb : d237696 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30204, d237696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30204, d237696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58038 (p : Pattern) (ha : d237700 p = 1) (hb : d238449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30098 q = 1) (hb : d237590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
    | true =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30099 q = 1) (hb : d237591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30100 q = 1) (hb : d237592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d237592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d237592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30101 q = 1) (hb : d237593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d237593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30101, d237593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d237599 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
    | true =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237600 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237601 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237601, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237601, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237602 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237602, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237602, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237603 q = 1) (hb : d238446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237603, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237603, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237618 q = 1) (hb : d238448 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237618, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237618, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237700 q = 1) (hb : d238449 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237700, d238449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237700, d238449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58039 (p : Pattern) (ha : d237706 p = 1) (hb : d238516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237697 q = 1) (hb : d238511 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237697, d238511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58037 q hb ha
    | true =>
      simp only [d237697, d238511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58019 q ha hb
  have h2 (q : Pattern) (ha : d237698 q = 1) (hb : d238512 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237698, d238512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237698, d238512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237699 q = 1) (hb : d238513 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237699, d238513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237699, d238513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237701 q = 1) (hb : d238450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237701, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58019 q ha hb
    | true =>
      simp only [d237701, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58038 q ha hb
  have h5 (q : Pattern) (ha : d237702 q = 1) (hb : d238451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237702, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237702, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237703 q = 1) (hb : d238452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237703, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237703, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237704 q = 1) (hb : d238514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237704, d238514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237704, d238514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237620 q = 1) (hb : d238450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237620, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58019 q ha hb
    | true =>
      simp only [d237620, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58022 q ha hb
  have h9 (q : Pattern) (ha : d237621 q = 1) (hb : d238451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237621, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237621, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237622 q = 1) (hb : d238452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237622, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237622, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237633 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58022 q ha hb
    | true =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58023 q ha hb
  have h12 (q : Pattern) (ha : d237634 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237635 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237636 q = 1) (hb : d238457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237636, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237636, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237705 q = 1) (hb : d238515 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237705, d238515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237705, d238515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237706 q = 1) (hb : d238516 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237706, d238516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237706, d238516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro58040 (p : Pattern) (ha : d237712 p = 1) (hb : d238522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237707 q = 1) (hb : d238517 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237707, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58039 q ha hb
    | true =>
      simp only [d237707, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237708 q = 1) (hb : d238518 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237708, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237708, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237709 q = 1) (hb : d238519 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237709, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237709, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237710 q = 1) (hb : d238520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237710, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237710, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237711 q = 1) (hb : d238521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237711, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237711, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237712 q = 1) (hb : d238522 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237712, d238522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237712, d238522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58041 (p : Pattern) (ha : d237720 p = 1) (hb : d238525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30309 q = 1) (hb : d237715 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30310 q = 1) (hb : d237716 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30310, d237716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30311 q = 1) (hb : d237717 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30311, d237717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237718 q = 1) (hb : d238439 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237718, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d237718, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237719 q = 1) (hb : d238440 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237719, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237719, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237720 q = 1) (hb : d238525 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237720, d238525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d237720, d238525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58042 (p : Pattern) (ha : d237726 p = 1) (hb : d238531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30098 q = 1) (hb : d237608 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58020 q ha hb
    | true =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30099 q = 1) (hb : d237609 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30100 q = 1) (hb : d237610 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d237610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d237610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30101 q = 1) (hb : d237611 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d237611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30101, d237611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d237613 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
    | true =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237614 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237615 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237615, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237615, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237616 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237616, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237616, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237617 q = 1) (hb : d238446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237617, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237617, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237721 q = 1) (hb : d238526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237721, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58041 q ha hb
    | true =>
      simp only [d237721, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237722 q = 1) (hb : d238527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237722, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237722, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237723 q = 1) (hb : d238528 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237723, d238528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237723, d238528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237724 q = 1) (hb : d238529 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237724, d238529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237724, d238529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237725 q = 1) (hb : d238530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237725, d238530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237725, d238530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237726 q = 1) (hb : d238531 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237726, d238531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237726, d238531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58043 (p : Pattern) (ha : d237729 p = 1) (hb : d238525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30309 q = 1) (hb : d237715 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30310 q = 1) (hb : d237727 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30310, d237727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30311 q = 1) (hb : d237728 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30311, d237728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30103 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30103, d237595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d237718 q = 1) (hb : d238439 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237718, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237718, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d237719 q = 1) (hb : d238440 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237719, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237719, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237729 q = 1) (hb : d238525 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237729, d238525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237729, d238525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro58044 (p : Pattern) (ha : d237735 p = 1) (hb : d238532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237730 q = 1) (hb : d238526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237730, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58043 q ha hb
    | true =>
      simp only [d237730, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237731 q = 1) (hb : d238527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237731, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237731, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237732 q = 1) (hb : d238528 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237732, d238528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237732, d238528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237733 q = 1) (hb : d238529 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237733, d238529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237733, d238529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237734 q = 1) (hb : d238530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237734, d238530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237734, d238530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237735 q = 1) (hb : d238532 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237735, d238532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237735, d238532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58045 (p : Pattern) (ha : d237741 p = 1) (hb : d238538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237620 q = 1) (hb : d238450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237620, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58019 q ha hb
    | true =>
      simp only [d237620, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58022 q ha hb
  have h2 (q : Pattern) (ha : d237621 q = 1) (hb : d238451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237621, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237621, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237622 q = 1) (hb : d238452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237622, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237622, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237633 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58022 q ha hb
    | true =>
      simp only [d237633, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58023 q ha hb
  have h5 (q : Pattern) (ha : d237634 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237635 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237636 q = 1) (hb : d238457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237636, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237636, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237736 q = 1) (hb : d238533 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237736, d238533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58042 q ha hb
    | true =>
      simp only [d237736, d238533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58044 q ha hb
  have h9 (q : Pattern) (ha : d237737 q = 1) (hb : d238534 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237737, d238534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237737, d238534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237738 q = 1) (hb : d238535 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237738, d238535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237738, d238535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237739 q = 1) (hb : d238536 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237739, d238536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237739, d238536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237740 q = 1) (hb : d238537 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237740, d238537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237740, d238537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237741 q = 1) (hb : d238538 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237741, d238538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237741, d238538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro58046 (p : Pattern) (ha : d237747 p = 1) (hb : d238544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237742 q = 1) (hb : d238539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237742, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58045 q ha hb
    | true =>
      simp only [d237742, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237743 q = 1) (hb : d238540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237743, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237743, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237744 q = 1) (hb : d238541 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237744, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237744, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237745 q = 1) (hb : d238542 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237745, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237745, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237746 q = 1) (hb : d238543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237746, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237746, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237747 q = 1) (hb : d238544 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237747, d238544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237747, d238544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58047 (p : Pattern) (ha : d237753 p = 1) (hb : d238550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237677 q = 1) (hb : d238498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237677, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58032 q ha hb
    | true =>
      simp only [d237677, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58033 q ha hb
  have h2 (q : Pattern) (ha : d237678 q = 1) (hb : d238499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237678, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237678, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237679 q = 1) (hb : d238500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237679, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237679, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237680 q = 1) (hb : d238501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237680, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237680, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237687 q = 1) (hb : d238508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237687, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58034 q ha hb
    | true =>
      simp only [d237687, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58035 q ha hb
  have h6 (q : Pattern) (ha : d237688 q = 1) (hb : d238509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237688, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237688, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237689 q = 1) (hb : d238510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237689, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237689, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237713 q = 1) (hb : d238523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237713, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58040 q ha hb
    | true =>
      simp only [d237713, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58026 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237714 q = 1) (hb : d238524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237714, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237748 q = 1) (hb : d238545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237748, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58046 q ha hb
    | true =>
      simp only [d237748, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237749 q = 1) (hb : d238546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237749, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237749, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237750 q = 1) (hb : d238547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237750, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237751 q = 1) (hb : d238548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237751, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237752 q = 1) (hb : d238549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237752, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237753 q = 1) (hb : d238550 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237753, d238550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237753, d238550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro58048 (p : Pattern) (ha : d237754 p = 1) (hb : d238551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237673 q = 1) (hb : d238494 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237673, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237673, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237754 q = 1) (hb : d238551 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237754, d238551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237754, d238551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58049 (p : Pattern) (ha : d237755 p = 1) (hb : d238552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237675 q = 1) (hb : d238496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237675, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237675, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237755 q = 1) (hb : d238552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237755, d238552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237755, d238552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58050 (p : Pattern) (ha : d237760 p = 1) (hb : d238557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237681 q = 1) (hb : d238502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237681, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237681, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237682 q = 1) (hb : d238503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237682, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237682, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237760 q = 1) (hb : d238557 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237760, d238557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237760, d238557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58051 (p : Pattern) (ha : d237761 p = 1) (hb : d238558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58025 q ha hb
    | true =>
      simp only [d237644, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237684 q = 1) (hb : d238505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237684, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237684, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237685 q = 1) (hb : d238506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237685, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237685, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237761 q = 1) (hb : d238558 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237761, d238558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237761, d238558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58052 (p : Pattern) (ha : d237765 p = 1) (hb : d238562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237707 q = 1) (hb : d238517 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237707, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58039 q ha hb
    | true =>
      simp only [d237707, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237708 q = 1) (hb : d238518 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237708, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237708, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237640 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58024 q ha hb
    | true =>
      simp only [d237640, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237641 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237709 q = 1) (hb : d238519 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237709, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237709, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237710 q = 1) (hb : d238520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237710, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237710, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237711 q = 1) (hb : d238521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237711, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237711, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237765 q = 1) (hb : d238562 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237765, d238562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237765, d238562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58053 (p : Pattern) (ha : d237768 p = 1) (hb : d238565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237742 q = 1) (hb : d238539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237742, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58045 q ha hb
    | true =>
      simp only [d237742, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237743 q = 1) (hb : d238540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237743, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237743, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237744 q = 1) (hb : d238541 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237744, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237744, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237745 q = 1) (hb : d238542 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237745, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237745, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237746 q = 1) (hb : d238543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237746, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237746, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237768 q = 1) (hb : d238565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237768, d238565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237768, d238565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58054 (p : Pattern) (ha : d237774 p = 1) (hb : d238571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237677 q = 1) (hb : d238498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237677, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58032 q ha hb
    | true =>
      simp only [d237677, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58033 q ha hb
  have h2 (q : Pattern) (ha : d237678 q = 1) (hb : d238499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237678, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237678, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237679 q = 1) (hb : d238500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237679, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237679, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237680 q = 1) (hb : d238501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237680, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237680, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237687 q = 1) (hb : d238508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237687, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58034 q ha hb
    | true =>
      simp only [d237687, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58035 q ha hb
  have h6 (q : Pattern) (ha : d237688 q = 1) (hb : d238509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237688, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237688, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237689 q = 1) (hb : d238510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237689, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237689, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237713 q = 1) (hb : d238523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237713, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58040 q ha hb
    | true =>
      simp only [d237713, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58026 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237714 q = 1) (hb : d238524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237714, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237748 q = 1) (hb : d238545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237748, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58046 q ha hb
    | true =>
      simp only [d237748, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237749 q = 1) (hb : d238546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237749, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237749, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237750 q = 1) (hb : d238547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237750, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237751 q = 1) (hb : d238548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237751, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237752 q = 1) (hb : d238549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237752, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237756 q = 1) (hb : d238553 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237756, d238553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58048 q ha hb
    | true =>
      simp only [d237756, d238553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58049 q ha hb
  have h17 (q : Pattern) (ha : d237757 q = 1) (hb : d238554 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237757, d238554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237757, d238554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237758 q = 1) (hb : d238555 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237758, d238555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237758, d238555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d237759 q = 1) (hb : d238556 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237759, d238556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237759, d238556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237762 q = 1) (hb : d238559 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237762, d238559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58050 q ha hb
    | true =>
      simp only [d237762, d238559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58051 q ha hb
  have h21 (q : Pattern) (ha : d237763 q = 1) (hb : d238560 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237763, d238560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237763, d238560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d237764 q = 1) (hb : d238561 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237764, d238561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237764, d238561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237766 q = 1) (hb : d238563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237766, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58052 q ha hb
    | true =>
      simp only [d237766, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58029 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d237664 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d237767 q = 1) (hb : d238564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d237767, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d237769 q = 1) (hb : d238566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237769, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58053 q ha hb
    | true =>
      simp only [d237769, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d237770 q = 1) (hb : d238567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237770, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d237770, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d237771 q = 1) (hb : d238568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d237771, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d237772 q = 1) (hb : d238569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237772, d238569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d237772, d238569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d237773 q = 1) (hb : d238570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237773, d238570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237773, d238570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d237774 q = 1) (hb : d238571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237774, d238571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237774, d238571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro58055 (p : Pattern) (ha : d237781 p = 1) (hb : d238578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237654 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58026 q ha hb
    | true =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58027 q ha hb
  have h2 (q : Pattern) (ha : d237655 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237655, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237655, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237656 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237656, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237656, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237657 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237657, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237657, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237658 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237658, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237658, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237776 q = 1) (hb : d238573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237776, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58027 q ha hb
    | true =>
      simp only [d237776, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237777 q = 1) (hb : d238574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237777, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237777, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237778 q = 1) (hb : d238575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237778, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237778, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237779 q = 1) (hb : d238576 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237779, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237779, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237780 q = 1) (hb : d238577 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237780, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237780, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237781 q = 1) (hb : d238578 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237781, d238578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237781, d238578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58056 (p : Pattern) (ha : d237787 p = 1) (hb : d238584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237776 q = 1) (hb : d238573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237776, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58027 q ha hb
    | true =>
      simp only [d237776, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237777 q = 1) (hb : d238574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237777, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237777, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237778 q = 1) (hb : d238575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237778, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237778, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237779 q = 1) (hb : d238576 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237779, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237779, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237780 q = 1) (hb : d238577 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237780, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237780, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237782 q = 1) (hb : d238579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237782, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58030 q ha hb
    | true =>
      simp only [d237782, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237783 q = 1) (hb : d238580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237783, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237783, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237784 q = 1) (hb : d238581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237784, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237784, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237785 q = 1) (hb : d238582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237785, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237785, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237786 q = 1) (hb : d238583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237786, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237786, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237787 q = 1) (hb : d238584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237787, d238584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237787, d238584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58057 (p : Pattern) (ha : d237794 p = 1) (hb : d238591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237766 q = 1) (hb : d238563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237766, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58052 q ha hb
    | true =>
      simp only [d237766, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58029 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237767 q = 1) (hb : d238564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237767, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237769 q = 1) (hb : d238566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237769, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58053 q ha hb
    | true =>
      simp only [d237769, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237770 q = 1) (hb : d238567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237770, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237770, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237771 q = 1) (hb : d238568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237771, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237792 q = 1) (hb : d238589 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237792, d238589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237792, d238589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237793 q = 1) (hb : d238590 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237793, d238590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237793, d238590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237794 q = 1) (hb : d238591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237794, d238591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237794, d238591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro58058 (p : Pattern) (ha : d237796 p = 1) (hb : d238593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237782 q = 1) (hb : d238579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237782, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58030 q ha hb
    | true =>
      simp only [d237782, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237783 q = 1) (hb : d238580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237783, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237783, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237784 q = 1) (hb : d238581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237784, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237784, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237785 q = 1) (hb : d238582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237785, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237785, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237786 q = 1) (hb : d238583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237786, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237786, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237796 q = 1) (hb : d238593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237796, d238593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237796, d238593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58059 (p : Pattern) (ha : d30413 p = 1) (hb : d237816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30399 q = 1) (hb : d237802 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30399, d237802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30399, d237802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58036 q ha hb
  have h2 (q : Pattern) (ha : d30199 q = 1) (hb : d237691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, d237691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58036 q ha hb
    | true =>
      simp only [d30199, d237691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30400 q = 1) (hb : d237803 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30400, d237803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30400, d237803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30200 q = 1) (hb : d237692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, d237692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30200, d237692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30401 q = 1) (hb : d237804 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30401, d237804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30401, d237804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30402 q = 1) (hb : d237805 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30402, d237805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30402, d237805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30403 q = 1) (hb : d237806 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, d237806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, d237806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58016 q ha hb
  have h8 (q : Pattern) (ha : d30088 q = 1) (hb : d237580 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58016 q ha hb
    | true =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30404 q = 1) (hb : d237807 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, d237807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30404, d237807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30089 q = 1) (hb : d237581 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30405 q = 1) (hb : d237808 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, d237808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30405, d237808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30406 q = 1) (hb : d237809 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, d237809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30406, d237809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30407 q = 1) (hb : d237810 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30407, d237810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30407, d237810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30408 q = 1) (hb : d237811 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d237811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d237811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
  have h15 (q : Pattern) (ha : d30098 q = 1) (hb : d237590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
    | true =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30409 q = 1) (hb : d237812 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d237812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30409, d237812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30099 q = 1) (hb : d237591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30410 q = 1) (hb : d237813 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d237813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30410, d237813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30411 q = 1) (hb : d237814 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d237814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d30411, d237814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d30412 q = 1) (hb : d237815 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, d237815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30412, d237815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d30413 q = 1) (hb : d237816 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30413, d237816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30413, d237816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58060 (p : Pattern) (ha : d237822 p = 1) (hb : d238604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30403 q = 1) (hb : d237806 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, d237806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, d237806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58016 q ha hb
  have h2 (q : Pattern) (ha : d30088 q = 1) (hb : d237580 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58016 q ha hb
    | true =>
      simp only [d30088, d237580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30404 q = 1) (hb : d237807 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, d237807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30404, d237807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30089 q = 1) (hb : d237581 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30089, d237581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30405 q = 1) (hb : d237808 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, d237808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30405, d237808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30406 q = 1) (hb : d237809 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, d237809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30406, d237809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30408 q = 1) (hb : d237811 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d237811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d237811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
  have h8 (q : Pattern) (ha : d30098 q = 1) (hb : d237590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
    | true =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30409 q = 1) (hb : d237812 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d237812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30409, d237812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30099 q = 1) (hb : d237591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30410 q = 1) (hb : d237813 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d237813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30410, d237813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30411 q = 1) (hb : d237814 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d237814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30411, d237814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30412 q = 1) (hb : d237815 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, d237815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30412, d237815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237817 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237817, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237817, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
  have h15 (q : Pattern) (ha : d237599 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
    | true =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237818 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237818, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237818, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237600 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237819 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237819, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237819, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237820 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237820, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237820, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237821 q = 1) (hb : d238603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237821, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d237821, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d237822 q = 1) (hb : d238604 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237822, d238604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d237822, d238604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58061 (p : Pattern) (ha : d237827 p = 1) (hb : d238609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30408 q = 1) (hb : d237811 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d237811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d237811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
  have h2 (q : Pattern) (ha : d30098 q = 1) (hb : d237590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58017 q ha hb
    | true =>
      simp only [d30098, d237590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30409 q = 1) (hb : d237812 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d237812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30409, d237812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30099 q = 1) (hb : d237591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30099, d237591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30410 q = 1) (hb : d237813 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d237813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30410, d237813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30411 q = 1) (hb : d237814 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d237814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30411, d237814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d237817 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237817, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237817, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
  have h8 (q : Pattern) (ha : d237599 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
    | true =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237818 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237818, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237818, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237600 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237819 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237819, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237819, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237820 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237820, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237820, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237821 q = 1) (hb : d238603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237821, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237821, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237826 q = 1) (hb : d238608 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237826, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237826, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237827 q = 1) (hb : d238609 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237827, d238609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237827, d238609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58062 (p : Pattern) (ha : d237841 p = 1) (hb : d238609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30408 q = 1) (hb : d237832 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d237832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d237832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58020 q ha hb
  have h2 (q : Pattern) (ha : d30098 q = 1) (hb : d237608 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58020 q ha hb
    | true =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30409 q = 1) (hb : d237833 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d237833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30409, d237833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30099 q = 1) (hb : d237609 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30410 q = 1) (hb : d237834 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d237834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30410, d237834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30411 q = 1) (hb : d237835 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d237835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30411, d237835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d237836 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237836, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237836, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
  have h8 (q : Pattern) (ha : d237613 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
    | true =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237837 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237837, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237837, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237614 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237838 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237838, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237838, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237839 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237839, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237839, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237840 q = 1) (hb : d238603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237840, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237840, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237817 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237817, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237817, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
  have h15 (q : Pattern) (ha : d237599 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58018 q ha hb
    | true =>
      simp only [d237599, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237818 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237818, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237818, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237600 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237600, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237819 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237819, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237819, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237820 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237820, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237820, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237826 q = 1) (hb : d238608 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237826, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237826, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237841 q = 1) (hb : d238609 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237841, d238609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237841, d238609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58063 (p : Pattern) (ha : d237851 p = 1) (hb : d238614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237836 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237836, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237836, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
  have h2 (q : Pattern) (ha : d237613 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
    | true =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237837 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237837, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237837, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237614 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237838 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237838, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237838, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237839 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237839, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237839, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237845 q = 1) (hb : d238608 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237845, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237845, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237850 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237851 q = 1) (hb : d238614 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237851, d238614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237851, d238614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro58064 (p : Pattern) (ha : d237857 p = 1) (hb : d238620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237823 q = 1) (hb : d238605 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237823, d238605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58059 q hb ha
    | true =>
      simp only [d237823, d238605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58060 q ha hb
  have h2 (q : Pattern) (ha : d237824 q = 1) (hb : d238606 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237824, d238606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237824, d238606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237825 q = 1) (hb : d238607 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237825, d238607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237825, d238607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237828 q = 1) (hb : d238610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237828, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58060 q ha hb
    | true =>
      simp only [d237828, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58061 q ha hb
  have h5 (q : Pattern) (ha : d237829 q = 1) (hb : d238611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237829, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237829, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237830 q = 1) (hb : d238612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237830, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237830, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237831 q = 1) (hb : d238613 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237831, d238613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237831, d238613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237842 q = 1) (hb : d238610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237842, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58060 q ha hb
    | true =>
      simp only [d237842, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58062 q ha hb
  have h9 (q : Pattern) (ha : d237843 q = 1) (hb : d238611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237843, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237843, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237844 q = 1) (hb : d238612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237844, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237844, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237852 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58062 q ha hb
    | true =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58063 q ha hb
  have h12 (q : Pattern) (ha : d237853 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237854 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237855 q = 1) (hb : d238618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237855, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237855, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237856 q = 1) (hb : d238619 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237856, d238619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237856, d238619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237857 q = 1) (hb : d238620 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237857, d238620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237857, d238620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro58065 (p : Pattern) (ha : d237862 p = 1) (hb : d238625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237842 q = 1) (hb : d238610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237842, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58060 q ha hb
    | true =>
      simp only [d237842, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58062 q ha hb
  have h2 (q : Pattern) (ha : d237843 q = 1) (hb : d238611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237843, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237843, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237844 q = 1) (hb : d238612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237844, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237844, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237852 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58062 q ha hb
    | true =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58063 q ha hb
  have h5 (q : Pattern) (ha : d237853 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237854 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237855 q = 1) (hb : d238618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237855, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237855, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237860 q = 1) (hb : d238623 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237860, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237860, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237861 q = 1) (hb : d238624 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237861, d238624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237861, d238624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237862 q = 1) (hb : d238625 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237862, d238625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237862, d238625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro58066 (p : Pattern) (ha : d237868 p = 1) (hb : d238631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237858 q = 1) (hb : d238621 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237858, d238621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58064 q ha hb
    | true =>
      simp only [d237858, d238621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237859 q = 1) (hb : d238622 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237859, d238622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237859, d238622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237863 q = 1) (hb : d238626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237863, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58065 q ha hb
    | true =>
      simp only [d237863, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237864 q = 1) (hb : d238627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237864, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237864, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237865 q = 1) (hb : d238628 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237865, d238628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237865, d238628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237866 q = 1) (hb : d238629 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237866, d238629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237866, d238629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237867 q = 1) (hb : d238630 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237867, d238630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237867, d238630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237868 q = 1) (hb : d238631 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237868, d238631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237868, d238631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58067 (p : Pattern) (ha : d237870 p = 1) (hb : d238633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237852 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58062 q ha hb
    | true =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58063 q ha hb
  have h2 (q : Pattern) (ha : d237853 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237854 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237860 q = 1) (hb : d238623 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237860, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237860, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237869 q = 1) (hb : d238632 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237869, d238632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237869, d238632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237870 q = 1) (hb : d238633 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237870, d238633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237870, d238633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58068 (p : Pattern) (ha : d237876 p = 1) (hb : d238639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237863 q = 1) (hb : d238626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237863, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58065 q ha hb
    | true =>
      simp only [d237863, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237864 q = 1) (hb : d238627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237864, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237864, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237871 q = 1) (hb : d238634 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237871, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58067 q ha hb
    | true =>
      simp only [d237871, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237872 q = 1) (hb : d238635 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237872, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237872, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237873 q = 1) (hb : d238636 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237873, d238636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237873, d238636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237874 q = 1) (hb : d238637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237874, d238637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237874, d238637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237875 q = 1) (hb : d238638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237875, d238638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237875, d238638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237876 q = 1) (hb : d238639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237876, d238639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237876, d238639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58069 (p : Pattern) (ha : d237889 p = 1) (hb : d238647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30408 q = 1) (hb : d237832 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d237832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d237832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58020 q ha hb
  have h2 (q : Pattern) (ha : d30098 q = 1) (hb : d237608 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58020 q ha hb
    | true =>
      simp only [d30098, d237608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30409 q = 1) (hb : d237833 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d237833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30409, d237833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30099 q = 1) (hb : d237609 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30099, d237609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30410 q = 1) (hb : d237834 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d237834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30410, d237834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30411 q = 1) (hb : d237835 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d237835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30411, d237835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d237836 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237836, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237836, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
  have h8 (q : Pattern) (ha : d237613 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58021 q ha hb
    | true =>
      simp only [d237613, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237837 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237837, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237837, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237614 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237614, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237838 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237838, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237838, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237839 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237839, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237839, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237840 q = 1) (hb : d238603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237840, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237840, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237884 q = 1) (hb : d238642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237884, d238642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237884, d238642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58041 q ha hb
  have h15 (q : Pattern) (ha : d237721 q = 1) (hb : d238526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237721, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58041 q ha hb
    | true =>
      simp only [d237721, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237885 q = 1) (hb : d238643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237885, d238643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237885, d238643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237722 q = 1) (hb : d238527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237722, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237722, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237886 q = 1) (hb : d238644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237886, d238644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237886, d238644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237887 q = 1) (hb : d238645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237887, d238645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237887, d238645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237888 q = 1) (hb : d238646 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237888, d238646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237888, d238646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237889 q = 1) (hb : d238647 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237889, d238647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237889, d238647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58070 (p : Pattern) (ha : d237895 p = 1) (hb : d238648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237890 q = 1) (hb : d238642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237890, d238642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237890, d238642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58043 q ha hb
  have h2 (q : Pattern) (ha : d237730 q = 1) (hb : d238526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237730, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58043 q ha hb
    | true =>
      simp only [d237730, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237891 q = 1) (hb : d238643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237891, d238643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237891, d238643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237731 q = 1) (hb : d238527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237731, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237731, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237892 q = 1) (hb : d238644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237892, d238644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237892, d238644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237893 q = 1) (hb : d238645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237893, d238645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237893, d238645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237894 q = 1) (hb : d238646 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237894, d238646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237894, d238646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237895 q = 1) (hb : d238648 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237895, d238648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237895, d238648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro58071 (p : Pattern) (ha : d237901 p = 1) (hb : d238654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237842 q = 1) (hb : d238610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237842, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58060 q ha hb
    | true =>
      simp only [d237842, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58062 q ha hb
  have h2 (q : Pattern) (ha : d237843 q = 1) (hb : d238611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237843, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237843, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237844 q = 1) (hb : d238612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237844, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237844, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237852 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58062 q ha hb
    | true =>
      simp only [d237852, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58063 q ha hb
  have h5 (q : Pattern) (ha : d237853 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237854 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237855 q = 1) (hb : d238618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237855, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237855, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237896 q = 1) (hb : d238649 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237896, d238649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58069 q ha hb
    | true =>
      simp only [d237896, d238649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58070 q ha hb
  have h9 (q : Pattern) (ha : d237897 q = 1) (hb : d238650 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237897, d238650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237897, d238650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237898 q = 1) (hb : d238651 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237898, d238651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237898, d238651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237899 q = 1) (hb : d238652 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237899, d238652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237899, d238652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237900 q = 1) (hb : d238653 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237900, d238653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237900, d238653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237901 q = 1) (hb : d238654 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237901, d238654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237901, d238654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro58072 (p : Pattern) (ha : d237907 p = 1) (hb : d238660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237902 q = 1) (hb : d238655 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237902, d238655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58071 q ha hb
    | true =>
      simp only [d237902, d238655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237903 q = 1) (hb : d238656 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237903, d238656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237903, d238656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237904 q = 1) (hb : d238657 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237904, d238657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237904, d238657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237905 q = 1) (hb : d238658 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237905, d238658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237905, d238658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237906 q = 1) (hb : d238659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237906, d238659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237906, d238659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237907 q = 1) (hb : d238660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237907, d238660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237907, d238660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58073 (p : Pattern) (ha : d237913 p = 1) (hb : d238666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237877 q = 1) (hb : d238640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237877, d238640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58066 q ha hb
    | true =>
      simp only [d237877, d238640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58068 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237882 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237883 q = 1) (hb : d238641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237883, d238641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237883, d238641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237908 q = 1) (hb : d238661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237908, d238661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58072 q ha hb
    | true =>
      simp only [d237908, d238661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237909 q = 1) (hb : d238662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237909, d238662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237909, d238662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237910 q = 1) (hb : d238663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237910, d238663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237910, d238663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237911 q = 1) (hb : d238664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237911, d238664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237911, d238664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237912 q = 1) (hb : d238665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237912, d238665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237912, d238665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237913 q = 1) (hb : d238666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237913, d238666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237913, d238666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro58074 (p : Pattern) (ha : d237881 p = 1) (hb : d238671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237871 q = 1) (hb : d238634 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237871, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58067 q ha hb
    | true =>
      simp only [d237871, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237872 q = 1) (hb : d238635 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237872, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237872, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237878 q = 1) (hb : d238668 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237878, d238668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237878, d238668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237879 q = 1) (hb : d238669 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237879, d238669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237879, d238669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237880 q = 1) (hb : d238670 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237880, d238670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237880, d238670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237881 q = 1) (hb : d238671 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237881, d238671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237881, d238671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58075 (p : Pattern) (ha : d237920 p = 1) (hb : d238677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237915 q = 1) (hb : d238672 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237915, d238672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58074 q ha hb
    | true =>
      simp only [d237915, d238672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237916 q = 1) (hb : d238673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237916, d238673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237916, d238673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237917 q = 1) (hb : d238674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237917, d238674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237917, d238674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237918 q = 1) (hb : d238675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237918, d238675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237918, d238675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237919 q = 1) (hb : d238676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237919, d238676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237919, d238676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237920 q = 1) (hb : d238677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237920, d238677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237920, d238677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58076 (p : Pattern) (ha : d237926 p = 1) (hb : d238683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237660 q = 1) (hb : d238481 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237660, d238481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237660, d238481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58028 q ha hb
  have h2 (q : Pattern) (ha : d237661 q = 1) (hb : d238482 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237661, d238482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237661, d238482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237670 q = 1) (hb : d238491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237670, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58028 q ha hb
    | true =>
      simp only [d237670, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58031 q ha hb
  have h4 (q : Pattern) (ha : d237671 q = 1) (hb : d238492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237671, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237671, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237672 q = 1) (hb : d238493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237672, d238493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237672, d238493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237775 q = 1) (hb : d238572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237775, d238572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58047 q ha hb
    | true =>
      simp only [d237775, d238572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58054 q ha hb
  have h7 (q : Pattern) (ha : d237788 q = 1) (hb : d238585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237788, d238585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58055 q ha hb
    | true =>
      simp only [d237788, d238585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58056 q ha hb
  have h8 (q : Pattern) (ha : d237789 q = 1) (hb : d238586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237789, d238586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237789, d238586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237790 q = 1) (hb : d238587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237790, d238587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237790, d238587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d237791 q = 1) (hb : d238588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237791, d238588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237791, d238588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237795 q = 1) (hb : d238592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237795, d238592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237795, d238592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58057 q ha hb
  have h12 (q : Pattern) (ha : d237797 q = 1) (hb : d238594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237797, d238594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237797, d238594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58058 q ha hb
  have h13 (q : Pattern) (ha : d237798 q = 1) (hb : d238595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237798, d238595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237798, d238595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237799 q = 1) (hb : d238596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237799, d238596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237799, d238596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237800 q = 1) (hb : d238597 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237800, d238597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237800, d238597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237801 q = 1) (hb : d238598 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237801, d238598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237801, d238598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237914 q = 1) (hb : d238667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237914, d238667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237914, d238667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58073 q ha hb
  have h18 (q : Pattern) (ha : d237921 q = 1) (hb : d238678 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237921, d238678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237921, d238678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58075 q ha hb
  have h19 (q : Pattern) (ha : d237922 q = 1) (hb : d238679 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237922, d238679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237922, d238679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237923 q = 1) (hb : d238680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237923, d238680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237923, d238680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237924 q = 1) (hb : d238681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237924, d238681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d237924, d238681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d237925 q = 1) (hb : d238682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237925, d238682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237925, d238682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237926 q = 1) (hb : d238683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237926, d238683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237926, d238683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro58077 (p : Pattern) (ha : d237932 p = 1) (hb : d238689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237927 q = 1) (hb : d238684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237927, d238684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237927, d238684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58076 q ha hb
  have h2 (q : Pattern) (ha : d237928 q = 1) (hb : d238685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237928, d238685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237928, d238685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237929 q = 1) (hb : d238686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237929, d238686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237929, d238686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237930 q = 1) (hb : d238687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237930, d238687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237930, d238687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237931 q = 1) (hb : d238688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237931, d238688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237931, d238688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237932 q = 1) (hb : d238689 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237932, d238689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237932, d238689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58078 (p : Pattern) (ha : d237938 p = 1) (hb : d238695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d211198 q = 1) (hb : d236679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211198, d236679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57805 q hb ha
    | true =>
      simp only [d211198, d236679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57847 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211238 q = 1) (hb : d236874 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211238, d236874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211238, d236874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57895 q ha hb
  have h3 (q : Pattern) (ha : d211239 q = 1) (hb : d236875 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211239, d236875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211239, d236875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237177 q = 1) (hb : d238212 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237177, d238212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237177, d238212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57951 q ha hb
  have h5 (q : Pattern) (ha : d237178 q = 1) (hb : d238213 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237178, d238213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237178, d238213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237179 q = 1) (hb : d238214 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237179, d238214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237179, d238214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237565 q = 1) (hb : d238435 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237565, d238435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237565, d238435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58015 q ha hb
  have h8 (q : Pattern) (ha : d237566 q = 1) (hb : d238436 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237566, d238436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237566, d238436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237567 q = 1) (hb : d238437 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237567, d238437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237567, d238437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237568 q = 1) (hb : d238438 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237568, d238438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237568, d238438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237933 q = 1) (hb : d238690 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237933, d238690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237933, d238690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58077 q ha hb
  have h12 (q : Pattern) (ha : d237934 q = 1) (hb : d238691 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237934, d238691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237934, d238691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237935 q = 1) (hb : d238692 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237935, d238692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237935, d238692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237936 q = 1) (hb : d238693 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237936, d238693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237936, d238693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237937 q = 1) (hb : d238694 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d237937, d238694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237937, d238694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237938 q = 1) (hb : d238695 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d237938, d238695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237938, d238695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro58079 (p : Pattern) (ha : d237944 p = 1) (hb : d238701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237939 q = 1) (hb : d238696 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d237939, d238696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58078 q ha hb
    | true =>
      simp only [d237939, d238696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237940 q = 1) (hb : d238697 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d237940, d238697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237940, d238697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237941 q = 1) (hb : d238698 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d237941, d238698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237941, d238698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237942 q = 1) (hb : d238699 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d237942, d238699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237942, d238699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237943 q = 1) (hb : d238700 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d237943, d238700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237943, d238700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237944 q = 1) (hb : d238701 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d237944, d238701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237944, d238701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58080 (p : Pattern) (ha : d237950 p = 1) (hb : d238707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237945 q = 1) (hb : d238702 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d237945, d238702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58079 q ha hb
    | true =>
      simp only [d237945, d238702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237946 q = 1) (hb : d238703 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d237946, d238703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237946, d238703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237947 q = 1) (hb : d238704 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d237947, d238704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237947, d238704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237948 q = 1) (hb : d238705 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d237948, d238705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237948, d238705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237949 q = 1) (hb : d238706 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d237949, d238706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237949, d238706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237950 q = 1) (hb : d238707 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d237950, d238707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237950, d238707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58081 (p : Pattern) (ha : d237956 p = 1) (hb : d238713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237951 q = 1) (hb : d238708 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d237951, d238708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58080 q ha hb
    | true =>
      simp only [d237951, d238708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237952 q = 1) (hb : d238709 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d237952, d238709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237952, d238709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237953 q = 1) (hb : d238710 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d237953, d238710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237953, d238710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237954 q = 1) (hb : d238711 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d237954, d238711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237954, d238711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237955 q = 1) (hb : d238712 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d237955, d238712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237955, d238712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237956 q = 1) (hb : d238713 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d237956, d238713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237956, d238713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58082 (p : Pattern) (ha : d237962 p = 1) (hb : d238719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237957 q = 1) (hb : d238714 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d237957, d238714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58081 q ha hb
    | true =>
      simp only [d237957, d238714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237958 q = 1) (hb : d238715 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d237958, d238715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237958, d238715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237959 q = 1) (hb : d238716 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d237959, d238716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237959, d238716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237960 q = 1) (hb : d238717 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d237960, d238717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237960, d238717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237961 q = 1) (hb : d238718 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d237961, d238718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237961, d238718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237962 q = 1) (hb : d238719 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d237962, d238719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237962, d238719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58083 (p : Pattern) (ha : d237968 p = 1) (hb : d238725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237963 q = 1) (hb : d238720 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d237963, d238720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58082 q ha hb
    | true =>
      simp only [d237963, d238720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237964 q = 1) (hb : d238721 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d237964, d238721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237964, d238721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237965 q = 1) (hb : d238722 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d237965, d238722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237965, d238722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237966 q = 1) (hb : d238723 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d237966, d238723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237966, d238723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237967 q = 1) (hb : d238724 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d237967, d238724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237967, d238724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237968 q = 1) (hb : d238725 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d237968, d238725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237968, d238725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58084 (p : Pattern) (ha : d237974 p = 1) (hb : d238731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237969 q = 1) (hb : d238726 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d237969, d238726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58083 q ha hb
    | true =>
      simp only [d237969, d238726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237970 q = 1) (hb : d238727 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d237970, d238727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237970, d238727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237971 q = 1) (hb : d238728 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d237971, d238728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237971, d238728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237972 q = 1) (hb : d238729 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d237972, d238729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237972, d238729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237973 q = 1) (hb : d238730 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d237973, d238730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237973, d238730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237974 q = 1) (hb : d238731 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d237974, d238731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237974, d238731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58085 (p : Pattern) (ha : d237980 p = 1) (hb : d238737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237975 q = 1) (hb : d238732 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d237975, d238732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58084 q ha hb
    | true =>
      simp only [d237975, d238732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237976 q = 1) (hb : d238733 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d237976, d238733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237976, d238733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237977 q = 1) (hb : d238734 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d237977, d238734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237977, d238734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237978 q = 1) (hb : d238735 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d237978, d238735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237978, d238735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237979 q = 1) (hb : d238736 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d237979, d238736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237979, d238736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237980 q = 1) (hb : d238737 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d237980, d238737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237980, d238737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58086 (p : Pattern) (ha : d53655 p = 1) (hb : d236582 p = 1) : d231169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d236582 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d236582 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d236582 q = 1) : d23208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d236582 q = 1) : d23209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d236582 q = 1) : d23210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d236582 q = 1) : d23211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d236582 q = 1) : d231169 q = 1 := by
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
theorem andIntro58087 (p : Pattern) (ha : d53665 p = 1) (hb : d236582 p = 1) : d231179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d236582 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d236582 q = 1) : d23184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57465 q ha hb
    | true =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d236582 q = 1) : d231175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d236582 q = 1) : d231176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d236582 q = 1) : d231177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d236582 q = 1) : d231178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d236582 q = 1) : d231179 q = 1 := by
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
theorem andIntro58088 (p : Pattern) (ha : d53671 p = 1) (hb : d236582 p = 1) : d231185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d236582 q = 1) : d23213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57471 q ha hb
    | true =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57472 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d236582 q = 1) : d23214 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d236582 q = 1) : d231167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d236582 q = 1) : d231168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d236582 q = 1) : d231170 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58086 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d236582 q = 1) : d231171 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d236582 q = 1) : d231172 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d236582 q = 1) : d231173 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d236582 q = 1) : d231174 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d236582 q = 1) : d231180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58087 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d236582 q = 1) : d231181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d236582 q = 1) : d231182 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d236582 q = 1) : d231183 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d236582 q = 1) : d231184 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d236582 q = 1) : d231185 q = 1 := by
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
theorem andIntro58089 (p : Pattern) (ha : d53677 p = 1) (hb : d236582 p = 1) : d231191 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d236582 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d236582 q = 1) : d231186 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58088 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d236582 q = 1) : d231187 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d236582 q = 1) : d231188 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d236582 q = 1) : d231189 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d236582 q = 1) : d231190 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d236582 q = 1) : d231191 q = 1 := by
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
theorem andIntro58090 (p : Pattern) (ha : d53680 p = 1) (hb : d236582 p = 1) : d231194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d502 q = 1) (hb : d236582 q = 1) : d23393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57500 q ha hb
    | true =>
      simp only [d502, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57501 q ha hb
  have h2 (q : Pattern) (ha : d503 q = 1) (hb : d236582 q = 1) : d23394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d236582 q = 1) : d23395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d504, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d236582 q = 1) : d23396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d236582 q = 1) : d23397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d236582 q = 1) : d231194 q = 1 := by
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
theorem andIntro58091 (p : Pattern) (ha : d53691 p = 1) (hb : d236582 p = 1) : d231205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53686 q = 1) (hb : d236582 q = 1) : d231200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57531 q ha hb
    | true =>
      simp only [d53686, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57507 q ha hb
  have h2 (q : Pattern) (ha : d53687 q = 1) (hb : d236582 q = 1) : d231201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d231201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d236582 q = 1) : d231202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53688, d231202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d236582 q = 1) : d231203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d231203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d236582 q = 1) : d231204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d231204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d236582 q = 1) : d231205 q = 1 := by
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
theorem andIntro58092 (p : Pattern) (ha : d53697 p = 1) (hb : d236582 p = 1) : d231211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d236582 q = 1) : d23399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57499 q ha hb
    | true =>
      simp only [d508, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57502 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d236582 q = 1) : d23400 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d236582 q = 1) : d231192 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d231192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d236582 q = 1) : d231193 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d231193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d236582 q = 1) : d231195 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d231195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58090 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d236582 q = 1) : d231196 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d231196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d236582 q = 1) : d231197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d231197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d236582 q = 1) : d231198 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d231198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d236582 q = 1) : d231199 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d231199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d236582 q = 1) : d231206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d231206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58091 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d236582 q = 1) : d231207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d231207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d236582 q = 1) : d231208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d231208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d236582 q = 1) : d231209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d231209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d236582 q = 1) : d231210 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d231210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d236582 q = 1) : d231211 q = 1 := by
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
theorem andIntro58093 (p : Pattern) (ha : d53703 p = 1) (hb : d236582 p = 1) : d231217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d236582 q = 1) : d231212 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d231212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58092 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d236582 q = 1) : d231213 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d231213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d236582 q = 1) : d231214 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d231214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d236582 q = 1) : d231215 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d231215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d236582 q = 1) : d231216 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d231216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d236582 q = 1) : d231217 q = 1 := by
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
theorem andIntro58094 (p : Pattern) (ha : d53707 p = 1) (hb : d236582 p = 1) : d231221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d794 q = 1) (hb : d236582 q = 1) : d23666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57545 q ha hb
    | true =>
      simp only [d794, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57546 q ha hb
  have h2 (q : Pattern) (ha : d795 q = 1) (hb : d236582 q = 1) : d23667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d236582 q = 1) : d23668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d796, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d236582 q = 1) : d23669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d236582 q = 1) : d23670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d236582 q = 1) : d231221 q = 1 := by
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
theorem andIntro58095 (p : Pattern) (ha : d53718 p = 1) (hb : d236582 p = 1) : d231232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53713 q = 1) (hb : d236582 q = 1) : d231227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57581 q ha hb
    | true =>
      simp only [d53713, d231227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57554 q ha hb
  have h2 (q : Pattern) (ha : d53714 q = 1) (hb : d236582 q = 1) : d231228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d231228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d236582 q = 1) : d231229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53715, d231229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d236582 q = 1) : d231230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d231230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d236582 q = 1) : d231231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d231231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d236582 q = 1) : d231232 q = 1 := by
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
theorem andIntro58096 (p : Pattern) (ha : d53724 p = 1) (hb : d236582 p = 1) : d231238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d236582 q = 1) : d23672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d23672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57544 q ha hb
    | true =>
      simp only [d800, d23672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57547 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d236582 q = 1) : d23673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d23673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d23673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d236582 q = 1) : d231219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d231219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d236582 q = 1) : d231220 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d231220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d236582 q = 1) : d231222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d231222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58094 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d236582 q = 1) : d231223 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d231223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d236582 q = 1) : d231224 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d231224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d236582 q = 1) : d231225 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d231225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d236582 q = 1) : d231226 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d231226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d236582 q = 1) : d231233 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d231233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58095 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d236582 q = 1) : d231234 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d231234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d236582 q = 1) : d231235 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d231235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d236582 q = 1) : d231236 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d231236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d236582 q = 1) : d231237 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d231237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d236582 q = 1) : d231238 q = 1 := by
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
theorem andIntro58097 (p : Pattern) (ha : d53730 p = 1) (hb : d236582 p = 1) : d231244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d236582 q = 1) : d231239 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d231239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58096 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d236582 q = 1) : d231240 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d231240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d236582 q = 1) : d231241 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d231241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d236582 q = 1) : d231242 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d231242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d236582 q = 1) : d231243 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d231243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d236582 q = 1) : d231244 q = 1 := by
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
theorem andIntro58098 (p : Pattern) (ha : d53735 p = 1) (hb : d236582 p = 1) : d238740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1173 q = 1) (hb : d236582 q = 1) : d238025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57600 q ha hb
    | true =>
      simp only [d1173, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57601 q ha hb
  have h2 (q : Pattern) (ha : d1174 q = 1) (hb : d236582 q = 1) : d238026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d236582 q = 1) : d238027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1175, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d236582 q = 1) : d238028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d236582 q = 1) : d238029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d236582 q = 1) : d238740 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58099 (p : Pattern) (ha : d53746 p = 1) (hb : d236582 p = 1) : d238751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53741 q = 1) (hb : d236582 q = 1) : d238746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d238746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57638 q ha hb
    | true =>
      simp only [d53741, d238746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57609 q ha hb
  have h2 (q : Pattern) (ha : d53742 q = 1) (hb : d236582 q = 1) : d238747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d236582 q = 1) : d238748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53743, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d236582 q = 1) : d238749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d236582 q = 1) : d238750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d236582 q = 1) : d238751 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58100 (p : Pattern) (ha : d53752 p = 1) (hb : d236582 p = 1) : d238757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d236582 q = 1) : d238031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57599 q ha hb
    | true =>
      simp only [d1179, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57602 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d236582 q = 1) : d238032 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d236582 q = 1) : d238738 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d236582 q = 1) : d238739 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d236582 q = 1) : d238741 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58098 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d236582 q = 1) : d238742 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d236582 q = 1) : d238743 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d236582 q = 1) : d238744 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d236582 q = 1) : d238745 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d236582 q = 1) : d238752 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58099 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d236582 q = 1) : d238753 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d236582 q = 1) : d238754 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d236582 q = 1) : d238755 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d236582 q = 1) : d238756 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d236582 q = 1) : d238757 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58101 (p : Pattern) (ha : d53758 p = 1) (hb : d236582 p = 1) : d238763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d236582 q = 1) : d238758 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58100 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d236582 q = 1) : d238759 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d236582 q = 1) : d238760 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d236582 q = 1) : d238761 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d236582 q = 1) : d238762 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d236582 q = 1) : d238763 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58102 (p : Pattern) (ha : d53764 p = 1) (hb : d236582 p = 1) : d238769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1634 q = 1) (hb : d236582 q = 1) : d238261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57658 q ha hb
    | true =>
      simp only [d1634, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57659 q ha hb
  have h2 (q : Pattern) (ha : d1635 q = 1) (hb : d236582 q = 1) : d238262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d236582 q = 1) : d238263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1636, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d236582 q = 1) : d238264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d236582 q = 1) : d238265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d236582 q = 1) : d238769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58103 (p : Pattern) (ha : d53775 p = 1) (hb : d236582 p = 1) : d238780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53770 q = 1) (hb : d236582 q = 1) : d238775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d238775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57696 q ha hb
    | true =>
      simp only [d53770, d238775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57667 q ha hb
  have h2 (q : Pattern) (ha : d53771 q = 1) (hb : d236582 q = 1) : d238776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d236582 q = 1) : d238777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53772, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d236582 q = 1) : d238778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d236582 q = 1) : d238779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d236582 q = 1) : d238780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58104 (p : Pattern) (ha : d53781 p = 1) (hb : d236582 p = 1) : d238786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d236582 q = 1) : d238267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57657 q ha hb
    | true =>
      simp only [d1640, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57660 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d236582 q = 1) : d238268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d236582 q = 1) : d238767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d236582 q = 1) : d238768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d236582 q = 1) : d238770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58102 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d236582 q = 1) : d238771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d236582 q = 1) : d238772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d236582 q = 1) : d238773 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d236582 q = 1) : d238774 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d236582 q = 1) : d238781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58103 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d236582 q = 1) : d238782 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d236582 q = 1) : d238783 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d236582 q = 1) : d238784 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d236582 q = 1) : d238785 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d236582 q = 1) : d238786 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58105 (p : Pattern) (ha : d53787 p = 1) (hb : d236582 p = 1) : d238792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d236582 q = 1) : d238787 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58104 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d236582 q = 1) : d238788 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d236582 q = 1) : d238789 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d236582 q = 1) : d238790 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d236582 q = 1) : d238791 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d236582 q = 1) : d238792 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58106 (p : Pattern) (ha : d53794 p = 1) (hb : d236582 p = 1) : d238799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2117 q = 1) (hb : d236582 q = 1) : d238485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57716 q ha hb
    | true =>
      simp only [d2117, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57717 q ha hb
  have h2 (q : Pattern) (ha : d2118 q = 1) (hb : d236582 q = 1) : d238486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d236582 q = 1) : d238487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2119, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d236582 q = 1) : d238488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d236582 q = 1) : d238489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d236582 q = 1) : d238799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58107 (p : Pattern) (ha : d53805 p = 1) (hb : d236582 p = 1) : d238810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53800 q = 1) (hb : d236582 q = 1) : d238805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d238805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57754 q ha hb
    | true =>
      simp only [d53800, d238805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57725 q ha hb
  have h2 (q : Pattern) (ha : d53801 q = 1) (hb : d236582 q = 1) : d238806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d236582 q = 1) : d238807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53802, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d236582 q = 1) : d238808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d236582 q = 1) : d238809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d236582 q = 1) : d238810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58108 (p : Pattern) (ha : d53811 p = 1) (hb : d236582 p = 1) : d238816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d236582 q = 1) : d238491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57715 q ha hb
    | true =>
      simp only [d2123, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57718 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d236582 q = 1) : d238492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d236582 q = 1) : d238797 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d236582 q = 1) : d238798 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d236582 q = 1) : d238800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58106 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d236582 q = 1) : d238801 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d236582 q = 1) : d238802 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d236582 q = 1) : d238803 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d236582 q = 1) : d238804 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d236582 q = 1) : d238811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58107 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d236582 q = 1) : d238812 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d236582 q = 1) : d238813 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d236582 q = 1) : d238814 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d236582 q = 1) : d238815 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d236582 q = 1) : d238816 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58109 (p : Pattern) (ha : d53817 p = 1) (hb : d236582 p = 1) : d238822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d236582 q = 1) : d238817 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58108 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d236582 q = 1) : d238818 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d236582 q = 1) : d238819 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d236582 q = 1) : d238820 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d236582 q = 1) : d238821 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d236582 q = 1) : d238822 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58110 (p : Pattern) (ha : d53823 p = 1) (hb : d236582 p = 1) : d238828 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d236582 q = 1) : d231218 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58089 q ha hb
    | true =>
      simp only [d53704, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58093 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d236582 q = 1) : d231245 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58097 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d236582 q = 1) : d231246 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d236582 q = 1) : d238764 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58101 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d236582 q = 1) : d238765 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d236582 q = 1) : d238766 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d236582 q = 1) : d238793 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58105 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d236582 q = 1) : d238794 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d236582 q = 1) : d238795 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d236582 q = 1) : d238796 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d236582 q = 1) : d238823 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58109 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d236582 q = 1) : d238824 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d236582 q = 1) : d238825 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d236582 q = 1) : d238826 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d236582 q = 1) : d238827 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d236582 q = 1) : d238828 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro58111 (p : Pattern) (ha : d53829 p = 1) (hb : d236582 p = 1) : d238834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d236582 q = 1) : d238829 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58110 q ha hb
    | true =>
      simp only [d53824, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d236582 q = 1) : d238830 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d236582 q = 1) : d238831 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d236582 q = 1) : d238832 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d236582 q = 1) : d238833 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d236582 q = 1) : d238834 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58112 (p : Pattern) (ha : d53835 p = 1) (hb : d236582 p = 1) : d238840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d236582 q = 1) : d238835 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58111 q ha hb
    | true =>
      simp only [d53830, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d236582 q = 1) : d238836 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d236582 q = 1) : d238837 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d236582 q = 1) : d238838 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d236582 q = 1) : d238839 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d236582 q = 1) : d238840 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58113 (p : Pattern) (ha : d53841 p = 1) (hb : d236583 p = 1) : d238846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d236583 q = 1) : d238841 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d236583, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58112 q ha hb
    | true =>
      simp only [d53836, d236583, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53837 q = 1) (hb : d236583 q = 1) : d238842 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53838 q = 1) (hb : d236583 q = 1) : d238843 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53838, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d53839 q = 1) (hb : d236583 q = 1) : d238844 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53839, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d53840 q = 1) (hb : d236583 q = 1) : d238845 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53840, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d53841 q = 1) (hb : d236583 q = 1) : d238846 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53841, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro58114 (p : Pattern) (ha : d53847 p = 1) (hb : d236583 p = 1) : d238852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d236583 q = 1) : d238847 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58113 q ha hb
    | true =>
      simp only [d53842, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d236583 q = 1) : d238848 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d236583 q = 1) : d238849 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d236583 q = 1) : d238850 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d236583 q = 1) : d238851 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d236583 q = 1) : d238852 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58115 (p : Pattern) (ha : d53853 p = 1) (hb : d236583 p = 1) : d238858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d236583 q = 1) : d238853 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58114 q ha hb
    | true =>
      simp only [d53848, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d236583 q = 1) : d238854 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d236583 q = 1) : d238855 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d236583 q = 1) : d238856 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d236583 q = 1) : d238857 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d236583 q = 1) : d238858 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58116 (p : Pattern) (ha : d53859 p = 1) (hb : d236583 p = 1) : d238864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d236583 q = 1) : d238859 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58115 q ha hb
    | true =>
      simp only [d53854, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d236583 q = 1) : d238860 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d236583 q = 1) : d238861 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d236583 q = 1) : d238862 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d236583 q = 1) : d238863 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d236583 q = 1) : d238864 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58117 (p : Pattern) (ha : d53865 p = 1) (hb : d236583 p = 1) : d238870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d236583 q = 1) : d238865 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58116 q ha hb
    | true =>
      simp only [d53860, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d236583 q = 1) : d238866 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d236583 q = 1) : d238867 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d236583 q = 1) : d238868 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d236583 q = 1) : d238869 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d236583 q = 1) : d238870 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58118 (p : Pattern) (ha : d23205 p = 1) (hb : d126892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23147 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57772 q ha hb
    | true =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d23201 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23201, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23202 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23202, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23203 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23203, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23204 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23204, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23205 q = 1) (hb : d126892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58119 (p : Pattern) (ha : d23212 p = 1) (hb : d126899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23147 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57772 q ha hb
    | true =>
      simp only [d23147, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d23201 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23201, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23202 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23202, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23203 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23203, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23204 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23154 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57774 q ha hb
    | true =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d23208 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23208, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23209 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23209, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23210 q = 1) (hb : d126897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23210, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23211 q = 1) (hb : d126898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23211, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23212 q = 1) (hb : d126899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23212, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58120 (p : Pattern) (ha : d126906 p = 1) (hb : d231169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57774 q ha hb
    | true =>
      simp only [d23154, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d23208 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23208, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23209 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23209, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23210 q = 1) (hb : d126904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23211 q = 1) (hb : d126905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126906 q = 1) (hb : d231169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126906, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126906, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro58121 (p : Pattern) (ha : d126930 p = 1) (hb : d231179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57779 q ha hb
    | true =>
      simp only [d23184, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d126926 q = 1) (hb : d231175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126926, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126926, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126927 q = 1) (hb : d231176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126927, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126927, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126928 q = 1) (hb : d231177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126928, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126928, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126929 q = 1) (hb : d231178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126929, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126929, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126930 q = 1) (hb : d231179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126930, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126930, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58122 (p : Pattern) (ha : d126936 p = 1) (hb : d231185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d126900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58118 q ha hb
    | true =>
      simp only [d23213, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58119 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23214 q = 1) (hb : d126901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126902 q = 1) (hb : d231167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126902, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d126902, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126903 q = 1) (hb : d231168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126903, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126903, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126907 q = 1) (hb : d231170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126907, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126907, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58120 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d126908 q = 1) (hb : d231171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126908, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126908, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d126909 q = 1) (hb : d231172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126909, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d126909, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d126910 q = 1) (hb : d231173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126910, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126910, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d126911 q = 1) (hb : d231174 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126911, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126911, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d126931 q = 1) (hb : d231180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126931, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126931, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58121 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d126932 q = 1) (hb : d231181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126932, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d126932, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d126933 q = 1) (hb : d231182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126933, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d126933, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d126934 q = 1) (hb : d231183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126934, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d126934, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d126935 q = 1) (hb : d231184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126935, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d126935, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d126936 q = 1) (hb : d231185 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d126936, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d126936, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58123 (p : Pattern) (ha : d126942 p = 1) (hb : d231191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126937 q = 1) (hb : d231186 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d126937, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126937, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58122 q ha hb
  have h8 (q : Pattern) (ha : d126938 q = 1) (hb : d231187 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d126938, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126938, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126939 q = 1) (hb : d231188 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d126939, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126939, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126940 q = 1) (hb : d231189 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d126940, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126940, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d126941 q = 1) (hb : d231190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d126941, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126941, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126942 q = 1) (hb : d231191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d126942, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126942, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58124 (p : Pattern) (ha : d23388 p = 1) (hb : d236619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23383 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57808 q ha hb
    | true =>
      simp only [d23383, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57809 q ha hb
  have h5 (q : Pattern) (ha : d23384 q = 1) (hb : d236615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d236615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23384, d236615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23385 q = 1) (hb : d236616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d236616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23385, d236616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23386 q = 1) (hb : d236617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d236617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23386, d236617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23387 q = 1) (hb : d236618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d236618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23387, d236618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23388 q = 1) (hb : d236619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d236619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d236619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58125 (p : Pattern) (ha : d23398 p = 1) (hb : d236626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23383 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23383, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57808 q ha hb
    | true =>
      simp only [d23383, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57809 q ha hb
  have h4 (q : Pattern) (ha : d23384 q = 1) (hb : d236615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d236615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23384, d236615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23385 q = 1) (hb : d236616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d236616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23385, d236616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23386 q = 1) (hb : d236617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d236617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23386, d236617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23387 q = 1) (hb : d236618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d236618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d236618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d236621 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23393 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57811 q ha hb
    | true =>
      simp only [d23393, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57812 q ha hb
  have h13 (q : Pattern) (ha : d23394 q = 1) (hb : d236622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d236622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23394, d236622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23395 q = 1) (hb : d236623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d236623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23395, d236623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23396 q = 1) (hb : d236624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d236624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23396, d236624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23397 q = 1) (hb : d236625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d236625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23397, d236625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23398 q = 1) (hb : d236626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d236626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23398, d236626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58126 (p : Pattern) (ha : d231194 p = 1) (hb : d236633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23393 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57811 q ha hb
    | true =>
      simp only [d23393, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57812 q ha hb
  have h3 (q : Pattern) (ha : d23394 q = 1) (hb : d236622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d236622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23394, d236622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23395 q = 1) (hb : d236623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d236623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23395, d236623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23396 q = 1) (hb : d236631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d236631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d236631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23397 q = 1) (hb : d236632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d236632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d236632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231194 q = 1) (hb : d236633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231194, d236633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231194, d236633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58127 (p : Pattern) (ha : d231205 p = 1) (hb : d236666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127079 q = 1) (hb : d231200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127079, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57843 q hb ha
    | true =>
      simp only [d127079, d231200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57818 q hb ha
  have h3 (q : Pattern) (ha : d231201 q = 1) (hb : d236662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231201, d236662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231201, d236662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231202 q = 1) (hb : d236663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231202, d236663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231202, d236663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231203 q = 1) (hb : d236664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231203, d236664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231203, d236664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231204 q = 1) (hb : d236665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231204, d236665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231204, d236665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231205 q = 1) (hb : d236666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231205, d236666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231205, d236666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58128 (p : Pattern) (ha : d231211 p = 1) (hb : d236672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d236627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d236627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58124 q ha hb
    | true =>
      simp only [d23399, d236627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58125 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23400 q = 1) (hb : d236628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d236628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d236628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231192 q = 1) (hb : d236629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231192, d236629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231192, d236629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231193 q = 1) (hb : d236630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231193, d236630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231193, d236630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231195 q = 1) (hb : d236634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231195, d236634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231195, d236634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58126 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d231196 q = 1) (hb : d236635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231196, d236635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231196, d236635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231197 q = 1) (hb : d236636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231197, d236636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231197, d236636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d231198 q = 1) (hb : d236637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231198, d236637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231198, d236637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d231199 q = 1) (hb : d236638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231199, d236638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231199, d236638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d231206 q = 1) (hb : d236667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231206, d236667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231206, d236667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58127 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d231207 q = 1) (hb : d236668 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231207, d236668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231207, d236668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d231208 q = 1) (hb : d236669 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231208, d236669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d231208, d236669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d231209 q = 1) (hb : d236670 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231209, d236670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d231209, d236670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d231210 q = 1) (hb : d236671 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231210, d236671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d231210, d236671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d231211 q = 1) (hb : d236672 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231211, d236672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231211, d236672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58129 (p : Pattern) (ha : d231217 p = 1) (hb : d236678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231212 q = 1) (hb : d236673 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231212, d236673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231212, d236673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58128 q ha hb
  have h2 (q : Pattern) (ha : d231213 q = 1) (hb : d236674 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231213, d236674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231213, d236674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231214 q = 1) (hb : d236675 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231214, d236675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231214, d236675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231215 q = 1) (hb : d236676 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231215, d236676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231215, d236676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231216 q = 1) (hb : d236677 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231216, d236677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231216, d236677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231217 q = 1) (hb : d236678 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231217, d236678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231217, d236678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58130 (p : Pattern) (ha : d23661 p = 1) (hb : d236775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236723 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236764 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23656 q = 1) (hb : d236694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d236694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57852 q ha hb
    | true =>
      simp only [d23656, d236694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57853 q ha hb
  have h5 (q : Pattern) (ha : d23657 q = 1) (hb : d236765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d236765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23657, d236765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d236771 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23658 q = 1) (hb : d236772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d236772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23658, d236772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23659 q = 1) (hb : d236773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d236773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23659, d236773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23660 q = 1) (hb : d236774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d236774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23660, d236774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23661 q = 1) (hb : d236775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d236775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d236775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58131 (p : Pattern) (ha : d23671 p = 1) (hb : d236794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23656 q = 1) (hb : d236694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23656, d236694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57852 q ha hb
    | true =>
      simp only [d23656, d236694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57853 q ha hb
  have h4 (q : Pattern) (ha : d23657 q = 1) (hb : d236765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d236765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23657, d236765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d236771 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23658 q = 1) (hb : d236772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d236772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23658, d236772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23659 q = 1) (hb : d236773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d236773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23659, d236773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23660 q = 1) (hb : d236774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d236774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d236774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d236780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d236784 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d236786 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d23666 q = 1) (hb : d236703 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d236703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57855 q ha hb
    | true =>
      simp only [d23666, d236703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57856 q ha hb
  have h13 (q : Pattern) (ha : d23667 q = 1) (hb : d236787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d236787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23667, d236787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d236790 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23668 q = 1) (hb : d236791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d236791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23668, d236791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23669 q = 1) (hb : d236792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d236792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23669, d236792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23670 q = 1) (hb : d236793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d236793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23670, d236793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23671 q = 1) (hb : d236794 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d236794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23671, d236794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58132 (p : Pattern) (ha : d231221 p = 1) (hb : d236803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236786 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23666 q = 1) (hb : d236703 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d236703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57855 q ha hb
    | true =>
      simp only [d23666, d236703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57856 q ha hb
  have h3 (q : Pattern) (ha : d23667 q = 1) (hb : d236787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d236787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23667, d236787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236790 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23668 q = 1) (hb : d236791 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d236791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23668, d236791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23669 q = 1) (hb : d236801 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d236801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d236801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23670 q = 1) (hb : d236802 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d236802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d236802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231221 q = 1) (hb : d236803 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231221, d236803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231221, d236803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58133 (p : Pattern) (ha : d231232 p = 1) (hb : d236861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231227 q = 1) (hb : d236850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231227, d236850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57891 q ha hb
    | true =>
      simp only [d231227, d236850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57863 q ha hb
  have h3 (q : Pattern) (ha : d231228 q = 1) (hb : d236851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231228, d236851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231228, d236851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231229 q = 1) (hb : d236858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231229, d236858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231229, d236858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231230 q = 1) (hb : d236859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231230, d236859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231230, d236859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231231 q = 1) (hb : d236860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231231, d236860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231231, d236860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231232 q = 1) (hb : d236861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231232, d236861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231232, d236861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58134 (p : Pattern) (ha : d231238 p = 1) (hb : d236867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236711 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d236795 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d236795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58130 q ha hb
    | true =>
      simp only [d23672, d236795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58131 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23673 q = 1) (hb : d236798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d236798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d236798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231219 q = 1) (hb : d236799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231219, d236799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231219, d236799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231220 q = 1) (hb : d236800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231220, d236800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231220, d236800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231222 q = 1) (hb : d236804 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231222, d236804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231222, d236804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58132 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d231223 q = 1) (hb : d236805 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231223, d236805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231223, d236805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231224 q = 1) (hb : d236806 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231224, d236806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231224, d236806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d231225 q = 1) (hb : d236807 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231225, d236807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231225, d236807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d231226 q = 1) (hb : d236808 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231226, d236808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231226, d236808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d231233 q = 1) (hb : d236862 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231233, d236862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231233, d236862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58133 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d231234 q = 1) (hb : d236863 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231234, d236863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231234, d236863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d231235 q = 1) (hb : d236864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231235, d236864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d231235, d236864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d231236 q = 1) (hb : d236865 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231236, d236865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d231236, d236865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d231237 q = 1) (hb : d236866 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231237, d236866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d231237, d236866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d231238 q = 1) (hb : d236867 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231238, d236867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231238, d236867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58135 (p : Pattern) (ha : d231244 p = 1) (hb : d236873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231239 q = 1) (hb : d236868 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231239, d236868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231239, d236868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58134 q ha hb
  have h2 (q : Pattern) (ha : d231240 q = 1) (hb : d236869 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231240, d236869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231240, d236869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231241 q = 1) (hb : d236870 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231241, d236870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231241, d236870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231242 q = 1) (hb : d236871 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231242, d236871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231242, d236871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231243 q = 1) (hb : d236872 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231243, d236872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231243, d236872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231244 q = 1) (hb : d236873 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231244, d236873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231244, d236873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58136 (p : Pattern) (ha : d237017 p = 1) (hb : d238020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236997 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d236930 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236930, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57903 q ha hb
    | true =>
      simp only [d236930, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57904 q ha hb
  have h5 (q : Pattern) (ha : d236998 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236998, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d236998, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237013 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237014 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237014, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237014, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237015 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237015, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237015, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237016 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237016, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237016, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237017 q = 1) (hb : d238020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237017, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237017, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58137 (p : Pattern) (ha : d237038 p = 1) (hb : d238030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236930 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236930, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57903 q ha hb
    | true =>
      simp only [d236930, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57904 q ha hb
  have h4 (q : Pattern) (ha : d236998 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236998, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d236998, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237013 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237014 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237014, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237014, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237015 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237015, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237015, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237016 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237016, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237016, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237023 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237028 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237030 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d236940 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236940, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57906 q ha hb
    | true =>
      simp only [d236940, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57907 q ha hb
  have h13 (q : Pattern) (ha : d237031 q = 1) (hb : d238026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237031, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237031, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237034 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237035 q = 1) (hb : d238027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237035, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237035, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237036 q = 1) (hb : d238028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237036, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237036, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237037 q = 1) (hb : d238029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237037, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237037, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237038 q = 1) (hb : d238030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237038, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237038, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58138 (p : Pattern) (ha : d237058 p = 1) (hb : d238740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236940 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236940, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57906 q ha hb
    | true =>
      simp only [d236940, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57907 q ha hb
  have h3 (q : Pattern) (ha : d237031 q = 1) (hb : d238026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237031, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237031, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237035 q = 1) (hb : d238027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237035, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237035, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237056 q = 1) (hb : d238028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237056, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237056, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237057 q = 1) (hb : d238029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237057, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237057, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237058 q = 1) (hb : d238740 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237058, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237058, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58139 (p : Pattern) (ha : d237157 p = 1) (hb : d238751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237137 q = 1) (hb : d238746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237137, d238746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57943 q ha hb
    | true =>
      simp only [d237137, d238746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57948 q ha hb
  have h3 (q : Pattern) (ha : d237138 q = 1) (hb : d238747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237138, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237138, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237154 q = 1) (hb : d238748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237154, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237154, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237155 q = 1) (hb : d238749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237155, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237155, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237156 q = 1) (hb : d238750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237156, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237156, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237157 q = 1) (hb : d238751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237157, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237157, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58140 (p : Pattern) (ha : d237170 p = 1) (hb : d238757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237039 q = 1) (hb : d238031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237039, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58136 q ha hb
    | true =>
      simp only [d237039, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58137 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237052 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237053 q = 1) (hb : d238032 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237053, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237053, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237054 q = 1) (hb : d238738 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237054, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237054, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237055 q = 1) (hb : d238739 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237055, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237055, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237059 q = 1) (hb : d238741 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237059, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237059, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58138 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237061 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237062 q = 1) (hb : d238742 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237062, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237062, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237063 q = 1) (hb : d238743 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237063, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237063, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237064 q = 1) (hb : d238744 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237064, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237064, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237065 q = 1) (hb : d238745 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237065, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237065, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237158 q = 1) (hb : d238752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237158, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237158, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58139 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237166 q = 1) (hb : d238753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237166, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237166, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237167 q = 1) (hb : d238754 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237167, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237167, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237168 q = 1) (hb : d238755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237168, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237168, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237169 q = 1) (hb : d238756 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237169, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237169, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237170 q = 1) (hb : d238757 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237170, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237170, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58141 (p : Pattern) (ha : d237176 p = 1) (hb : d238763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237171 q = 1) (hb : d238758 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237171, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237171, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58140 q ha hb
  have h2 (q : Pattern) (ha : d237172 q = 1) (hb : d238759 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237172, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237172, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237173 q = 1) (hb : d238760 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237173, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237173, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237174 q = 1) (hb : d238761 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237174, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237174, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237175 q = 1) (hb : d238762 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237175, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237175, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237176 q = 1) (hb : d238763 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237176, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237176, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58142 (p : Pattern) (ha : d237376 p = 1) (hb : d238256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237276 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57963 q ha hb
    | true =>
      simp only [d237276, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57964 q ha hb
  have h5 (q : Pattern) (ha : d237342 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237342, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237372 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237373 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237373, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237374 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237374, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237375 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237375, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237376 q = 1) (hb : d238256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237376, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237376, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58143 (p : Pattern) (ha : d237397 p = 1) (hb : d238266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237341 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237276 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57963 q ha hb
    | true =>
      simp only [d237276, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57964 q ha hb
  have h4 (q : Pattern) (ha : d237342 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237342, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237373 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237373, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237374 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237374, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237375 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237375, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d237286 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237286, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57966 q ha hb
    | true =>
      simp only [d237286, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57967 q ha hb
  have h13 (q : Pattern) (ha : d237390 q = 1) (hb : d238262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237390, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237394 q = 1) (hb : d238263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237394, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237395 q = 1) (hb : d238264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237395, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237395, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237396 q = 1) (hb : d238265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237396, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237396, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237397 q = 1) (hb : d238266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237397, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237397, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58144 (p : Pattern) (ha : d237417 p = 1) (hb : d238769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237286 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237286, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57966 q ha hb
    | true =>
      simp only [d237286, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57967 q ha hb
  have h3 (q : Pattern) (ha : d237390 q = 1) (hb : d238262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237390, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237394 q = 1) (hb : d238263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237394, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237415 q = 1) (hb : d238264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237415, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237415, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237416 q = 1) (hb : d238265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237416, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237416, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237417 q = 1) (hb : d238769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237417, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237417, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58145 (p : Pattern) (ha : d237545 p = 1) (hb : d238780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237509 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237514 q = 1) (hb : d238775 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237514, d238775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58006 q ha hb
    | true =>
      simp only [d237514, d238775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58012 q ha hb
  have h3 (q : Pattern) (ha : d237515 q = 1) (hb : d238776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237515, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237515, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237541 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237542 q = 1) (hb : d238777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237542, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237542, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237543 q = 1) (hb : d238778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237543, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237543, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237544 q = 1) (hb : d238779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237544, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237544, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237545 q = 1) (hb : d238780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237545, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237545, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58146 (p : Pattern) (ha : d237558 p = 1) (hb : d238786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237398 q = 1) (hb : d238267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237398, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58142 q ha hb
    | true =>
      simp only [d237398, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58143 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237412 q = 1) (hb : d238268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237412, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237412, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237413 q = 1) (hb : d238767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237413, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237413, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237414 q = 1) (hb : d238768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237414, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237414, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237418 q = 1) (hb : d238770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237418, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237418, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58144 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237420 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237421 q = 1) (hb : d238771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237421, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237421, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237422 q = 1) (hb : d238772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237422, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237422, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237423 q = 1) (hb : d238773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237423, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237423, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237424 q = 1) (hb : d238774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237424, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237424, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237546 q = 1) (hb : d238781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237546, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237546, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58145 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237553 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237554 q = 1) (hb : d238782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237554, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237554, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237555 q = 1) (hb : d238783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237555, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237555, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237556 q = 1) (hb : d238784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237556, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237556, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237557 q = 1) (hb : d238785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237557, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237557, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237558 q = 1) (hb : d238786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237558, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237558, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58147 (p : Pattern) (ha : d237564 p = 1) (hb : d238792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237559 q = 1) (hb : d238787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237559, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237559, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58146 q ha hb
  have h2 (q : Pattern) (ha : d237560 q = 1) (hb : d238788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237560, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237560, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237561 q = 1) (hb : d238789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237561, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237561, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237562 q = 1) (hb : d238790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237562, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237562, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237563 q = 1) (hb : d238791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237563, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237563, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237564 q = 1) (hb : d238792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237564, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237564, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58148 (p : Pattern) (ha : d237753 p = 1) (hb : d238480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237680 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237713 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237654 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58026 q ha hb
    | true =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58027 q ha hb
  have h5 (q : Pattern) (ha : d237714 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237714, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237749 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237750 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237750, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237751 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237751, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237752 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237752, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237753 q = 1) (hb : d238480 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237753, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237753, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58149 (p : Pattern) (ha : d237774 p = 1) (hb : d238490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237654 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58026 q ha hb
    | true =>
      simp only [d237654, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58027 q ha hb
  have h4 (q : Pattern) (ha : d237714 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237714, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237750 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237750, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237751 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237751, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237752 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237752, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237764 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237766 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d237664 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237664, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58029 q ha hb
    | true =>
      simp only [d237664, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58030 q ha hb
  have h13 (q : Pattern) (ha : d237767 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237767, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237770 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237771 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237771, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237772 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237772, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237772, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237773 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237773, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237773, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237774 q = 1) (hb : d238490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237774, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237774, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58150 (p : Pattern) (ha : d237794 p = 1) (hb : d238799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237664 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237664, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58029 q ha hb
    | true =>
      simp only [d237664, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58030 q ha hb
  have h3 (q : Pattern) (ha : d237767 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237767, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237770 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237771 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237771, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237792 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237792, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237792, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237793 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237793, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237793, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237794 q = 1) (hb : d238799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237794, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237794, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58151 (p : Pattern) (ha : d237913 p = 1) (hb : d238810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237877 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237882 q = 1) (hb : d238805 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237882, d238805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58068 q ha hb
    | true =>
      simp only [d237882, d238805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58074 q ha hb
  have h3 (q : Pattern) (ha : d237883 q = 1) (hb : d238806 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237883, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237883, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237909 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237910 q = 1) (hb : d238807 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237910, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237910, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237911 q = 1) (hb : d238808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237911, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237911, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237912 q = 1) (hb : d238809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237912, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237912, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237913 q = 1) (hb : d238810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237913, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237913, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58152 (p : Pattern) (ha : d237926 p = 1) (hb : d238816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237775 q = 1) (hb : d238491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237775, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58148 q ha hb
    | true =>
      simp only [d237775, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58149 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237788 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237789 q = 1) (hb : d238492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237789, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237789, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237790 q = 1) (hb : d238797 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237790, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237790, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237791 q = 1) (hb : d238798 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237791, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237791, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237795 q = 1) (hb : d238800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237795, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237795, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58150 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237797 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237798 q = 1) (hb : d238801 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237798, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237798, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237799 q = 1) (hb : d238802 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237799, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237799, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237800 q = 1) (hb : d238803 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237800, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237800, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237801 q = 1) (hb : d238804 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237801, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237801, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237914 q = 1) (hb : d238811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237914, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237914, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58151 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237921 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237922 q = 1) (hb : d238812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237922, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237922, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237923 q = 1) (hb : d238813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237923, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237923, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237924 q = 1) (hb : d238814 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237924, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237924, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237925 q = 1) (hb : d238815 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237925, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237925, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237926 q = 1) (hb : d238816 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237926, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237926, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58153 (p : Pattern) (ha : d237932 p = 1) (hb : d238822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237927 q = 1) (hb : d238817 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237927, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237927, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58152 q ha hb
  have h2 (q : Pattern) (ha : d237928 q = 1) (hb : d238818 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237928, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237928, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237929 q = 1) (hb : d238819 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237929, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237929, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237930 q = 1) (hb : d238820 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237930, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237930, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237931 q = 1) (hb : d238821 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237931, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237931, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237932 q = 1) (hb : d238822 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237932, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237932, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58154 (p : Pattern) (ha : d237938 p = 1) (hb : d238828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d231218 q = 1) (hb : d236679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231218, d236679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58123 q hb ha
    | true =>
      simp only [d231218, d236679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58129 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231245 q = 1) (hb : d236874 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231245, d236874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231245, d236874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58135 q ha hb
  have h3 (q : Pattern) (ha : d231246 q = 1) (hb : d236875 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231246, d236875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231246, d236875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237177 q = 1) (hb : d238764 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237177, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237177, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58141 q ha hb
  have h5 (q : Pattern) (ha : d237178 q = 1) (hb : d238765 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237178, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237178, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237179 q = 1) (hb : d238766 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237179, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237179, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237565 q = 1) (hb : d238793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237565, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237565, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58147 q ha hb
  have h8 (q : Pattern) (ha : d237566 q = 1) (hb : d238794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237566, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237566, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237567 q = 1) (hb : d238795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237567, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237567, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237568 q = 1) (hb : d238796 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237568, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237568, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237933 q = 1) (hb : d238823 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237933, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237933, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58153 q ha hb
  have h12 (q : Pattern) (ha : d237934 q = 1) (hb : d238824 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237934, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237934, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237935 q = 1) (hb : d238825 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237935, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237935, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237936 q = 1) (hb : d238826 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237936, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237936, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237937 q = 1) (hb : d238827 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d237937, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237937, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237938 q = 1) (hb : d238828 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d237938, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237938, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro58155 (p : Pattern) (ha : d237944 p = 1) (hb : d238834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237939 q = 1) (hb : d238829 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d237939, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58154 q ha hb
    | true =>
      simp only [d237939, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237940 q = 1) (hb : d238830 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d237940, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237940, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237941 q = 1) (hb : d238831 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d237941, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237941, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237942 q = 1) (hb : d238832 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d237942, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237942, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237943 q = 1) (hb : d238833 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d237943, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237943, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237944 q = 1) (hb : d238834 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d237944, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237944, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58156 (p : Pattern) (ha : d237950 p = 1) (hb : d238840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237945 q = 1) (hb : d238835 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d237945, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58155 q ha hb
    | true =>
      simp only [d237945, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237946 q = 1) (hb : d238836 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d237946, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237946, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237947 q = 1) (hb : d238837 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d237947, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237947, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237948 q = 1) (hb : d238838 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d237948, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237948, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237949 q = 1) (hb : d238839 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d237949, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237949, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237950 q = 1) (hb : d238840 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d237950, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237950, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58157 (p : Pattern) (ha : d237956 p = 1) (hb : d238846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237951 q = 1) (hb : d238841 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d237951, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58156 q ha hb
    | true =>
      simp only [d237951, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237952 q = 1) (hb : d238842 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d237952, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237952, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237953 q = 1) (hb : d238843 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d237953, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237953, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237954 q = 1) (hb : d238844 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d237954, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237954, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237955 q = 1) (hb : d238845 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d237955, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237955, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237956 q = 1) (hb : d238846 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d237956, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237956, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58158 (p : Pattern) (ha : d237962 p = 1) (hb : d238852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237957 q = 1) (hb : d238847 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d237957, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58157 q ha hb
    | true =>
      simp only [d237957, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237958 q = 1) (hb : d238848 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d237958, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237958, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237959 q = 1) (hb : d238849 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d237959, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237959, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237960 q = 1) (hb : d238850 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d237960, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237960, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237961 q = 1) (hb : d238851 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d237961, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237961, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237962 q = 1) (hb : d238852 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d237962, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237962, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58159 (p : Pattern) (ha : d237968 p = 1) (hb : d238858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237963 q = 1) (hb : d238853 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d237963, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58158 q ha hb
    | true =>
      simp only [d237963, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237964 q = 1) (hb : d238854 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d237964, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237964, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237965 q = 1) (hb : d238855 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d237965, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237965, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237966 q = 1) (hb : d238856 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d237966, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237966, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237967 q = 1) (hb : d238857 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d237967, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237967, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237968 q = 1) (hb : d238858 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d237968, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237968, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58160 (p : Pattern) (ha : d237974 p = 1) (hb : d238864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237969 q = 1) (hb : d238859 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d237969, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58159 q ha hb
    | true =>
      simp only [d237969, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237970 q = 1) (hb : d238860 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d237970, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237970, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237971 q = 1) (hb : d238861 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d237971, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237971, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237972 q = 1) (hb : d238862 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d237972, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237972, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237973 q = 1) (hb : d238863 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d237973, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237973, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237974 q = 1) (hb : d238864 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d237974, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237974, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58161 (p : Pattern) (ha : d237980 p = 1) (hb : d238870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237975 q = 1) (hb : d238865 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d237975, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58160 q ha hb
    | true =>
      simp only [d237975, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237976 q = 1) (hb : d238866 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d237976, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237976, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237977 q = 1) (hb : d238867 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d237977, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237977, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237978 q = 1) (hb : d238868 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d237978, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237978, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237979 q = 1) (hb : d238869 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d237979, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237979, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237980 q = 1) (hb : d238870 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d237980, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237980, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro58162 (p : Pattern) (ha : d23205 p = 1) (hb : d128195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23201 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23201, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23202 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23202, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23203 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23203, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23204 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23204, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23205 q = 1) (hb : d128195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23205, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23205, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58163 (p : Pattern) (ha : d23212 p = 1) (hb : d128200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23201 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23201, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23201, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23202 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23202, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23202, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23203 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23203, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23203, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23204 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23204, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23204, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23208 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23208, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23209 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23209, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23210 q = 1) (hb : d128198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23210, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23211 q = 1) (hb : d128199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23211, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23212 q = 1) (hb : d128200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23212, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23212, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58164 (p : Pattern) (ha : d128207 p = 1) (hb : d231169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23208 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23208, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23209 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23209, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23210 q = 1) (hb : d128205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23211 q = 1) (hb : d128206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d231169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d231169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro58165 (p : Pattern) (ha : d128217 p = 1) (hb : d231179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128213 q = 1) (hb : d231175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128213, d231175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d231176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128214, d231176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d231177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d231177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d231178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d231178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d231179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d231179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58166 (p : Pattern) (ha : d128223 p = 1) (hb : d231185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d128201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58162 q ha hb
    | true =>
      simp only [d23213, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58163 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23214 q = 1) (hb : d128202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128203 q = 1) (hb : d231167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128203, d231167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128204 q = 1) (hb : d231168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128204, d231168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128208 q = 1) (hb : d231170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128208, d231170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58164 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128209 q = 1) (hb : d231171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128209, d231171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128210 q = 1) (hb : d231172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128210, d231172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128211 q = 1) (hb : d231173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128211, d231173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128212 q = 1) (hb : d231174 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128212, d231174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128218 q = 1) (hb : d231180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128218, d231180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58165 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128219 q = 1) (hb : d231181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128219, d231181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128220 q = 1) (hb : d231182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128220, d231182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128221 q = 1) (hb : d231183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128221, d231183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128222 q = 1) (hb : d231184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128222, d231184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128223 q = 1) (hb : d231185 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128223, d231185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58167 (p : Pattern) (ha : d128229 p = 1) (hb : d231191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d231186 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d231186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58166 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d231187 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d231187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d231188 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d231188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d231189 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d231189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d231190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d231190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d231191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d231191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58168 (p : Pattern) (ha : d23388 p = 1) (hb : d238875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28769 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23383 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23384 q = 1) (hb : d238871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d238871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23384, d238871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23385 q = 1) (hb : d238872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d238872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23385, d238872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23386 q = 1) (hb : d238873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d238873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23386, d238873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23387 q = 1) (hb : d238874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d238874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23387, d238874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23388 q = 1) (hb : d238875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23388, d238875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23388, d238875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58169 (p : Pattern) (ha : d23398 p = 1) (hb : d238880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28769 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23383 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23384 q = 1) (hb : d238871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23384, d238871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23384, d238871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23385 q = 1) (hb : d238872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23385, d238872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23385, d238872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23386 q = 1) (hb : d238873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23386, d238873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23386, d238873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23387 q = 1) (hb : d238874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23387, d238874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23387, d238874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16125 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16129 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d28776 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23393 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23394 q = 1) (hb : d238876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d238876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23394, d238876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23395 q = 1) (hb : d238877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d238877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23395, d238877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23396 q = 1) (hb : d238878 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d238878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23396, d238878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23397 q = 1) (hb : d238879 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d238879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23397, d238879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23398 q = 1) (hb : d238880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23398, d238880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23398, d238880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58170 (p : Pattern) (ha : d231194 p = 1) (hb : d238887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23394 q = 1) (hb : d238876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d238876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23394, d238876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23395 q = 1) (hb : d238877 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d238877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23395, d238877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23396 q = 1) (hb : d238885 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d238885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d238885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23397 q = 1) (hb : d238886 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d238886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d238886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231194 q = 1) (hb : d238887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231194, d238887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231194, d238887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58171 (p : Pattern) (ha : d231205 p = 1) (hb : d238897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d231201 q = 1) (hb : d238893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231201, d238893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231201, d238893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231202 q = 1) (hb : d238894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231202, d238894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231202, d238894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231203 q = 1) (hb : d238895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231203, d238895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231203, d238895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231204 q = 1) (hb : d238896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231204, d238896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231204, d238896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231205 q = 1) (hb : d238897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231205, d238897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231205, d238897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58172 (p : Pattern) (ha : d231211 p = 1) (hb : d238903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d238881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d238881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58168 q ha hb
    | true =>
      simp only [d23399, d238881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58169 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23400 q = 1) (hb : d238882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d238882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d238882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231192 q = 1) (hb : d238883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231192, d238883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231192, d238883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231193 q = 1) (hb : d238884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231193, d238884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231193, d238884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231195 q = 1) (hb : d238888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231195, d238888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231195, d238888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58170 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d231196 q = 1) (hb : d238889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231196, d238889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231196, d238889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231197 q = 1) (hb : d238890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231197, d238890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231197, d238890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d231198 q = 1) (hb : d238891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231198, d238891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231198, d238891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d231199 q = 1) (hb : d238892 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231199, d238892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231199, d238892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d231206 q = 1) (hb : d238898 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231206, d238898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231206, d238898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58171 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d231207 q = 1) (hb : d238899 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231207, d238899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231207, d238899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d231208 q = 1) (hb : d238900 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231208, d238900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d231208, d238900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d231209 q = 1) (hb : d238901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231209, d238901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d231209, d238901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d231210 q = 1) (hb : d238902 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231210, d238902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d231210, d238902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d231211 q = 1) (hb : d238903 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231211, d238903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231211, d238903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58173 (p : Pattern) (ha : d231217 p = 1) (hb : d238909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231212 q = 1) (hb : d238904 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231212, d238904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231212, d238904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58172 q ha hb
  have h2 (q : Pattern) (ha : d231213 q = 1) (hb : d238905 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231213, d238905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231213, d238905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231214 q = 1) (hb : d238906 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231214, d238906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231214, d238906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231215 q = 1) (hb : d238907 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231215, d238907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231215, d238907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231216 q = 1) (hb : d238908 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231216, d238908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231216, d238908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231217 q = 1) (hb : d238909 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231217, d238909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231217, d238909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58174 (p : Pattern) (ha : d23661 p = 1) (hb : d238915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28919 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23657 q = 1) (hb : d238911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d238911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23657, d238911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d28958 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d23658 q = 1) (hb : d238912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d238912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23658, d238912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23659 q = 1) (hb : d238913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d238913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23659, d238913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23660 q = 1) (hb : d238914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d238914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23660, d238914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23661 q = 1) (hb : d238915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23661, d238915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23661, d238915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58175 (p : Pattern) (ha : d23671 p = 1) (hb : d238920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23656 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d23657 q = 1) (hb : d238911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23657, d238911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23657, d238911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d28958 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d23658 q = 1) (hb : d238912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23658, d238912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23658, d238912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23659 q = 1) (hb : d238913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23659, d238913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23659, d238913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23660 q = 1) (hb : d238914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23660, d238914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23660, d238914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d28967 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d28971 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d28973 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d23666 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23667 q = 1) (hb : d238916 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d238916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23667, d238916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28979 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23668 q = 1) (hb : d238917 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d238917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23668, d238917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23669 q = 1) (hb : d238918 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d238918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23669, d238918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23670 q = 1) (hb : d238919 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d238919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23670, d238919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d23671 q = 1) (hb : d238920 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23671, d238920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23671, d238920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58176 (p : Pattern) (ha : d231221 p = 1) (hb : d238927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28973 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23666 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23667 q = 1) (hb : d238916 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d238916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23667, d238916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28979 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d23668 q = 1) (hb : d238917 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d238917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23668, d238917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23669 q = 1) (hb : d238925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d238925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d238925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23670 q = 1) (hb : d238926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d238926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d238926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231221 q = 1) (hb : d238927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231221, d238927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231221, d238927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58177 (p : Pattern) (ha : d231232 p = 1) (hb : d238937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d231227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d231228 q = 1) (hb : d238933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231228, d238933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231228, d238933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29069 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231229 q = 1) (hb : d238934 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231229, d238934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231229, d238934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231230 q = 1) (hb : d238935 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231230, d238935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231230, d238935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231231 q = 1) (hb : d238936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231231, d238936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231231, d238936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d231232 q = 1) (hb : d238937 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231232, d238937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231232, d238937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58178 (p : Pattern) (ha : d231238 p = 1) (hb : d238943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d238921 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d238921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58174 q ha hb
    | true =>
      simp only [d23672, d238921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58175 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28986 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d23673 q = 1) (hb : d238922 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d238922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d238922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d231219 q = 1) (hb : d238923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231219, d238923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231219, d238923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231220 q = 1) (hb : d238924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231220, d238924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231220, d238924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231222 q = 1) (hb : d238928 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231222, d238928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231222, d238928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58176 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d231223 q = 1) (hb : d238929 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231223, d238929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231223, d238929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231224 q = 1) (hb : d238930 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231224, d238930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231224, d238930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d231225 q = 1) (hb : d238931 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231225, d238931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231225, d238931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d231226 q = 1) (hb : d238932 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231226, d238932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231226, d238932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d231233 q = 1) (hb : d238938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231233, d238938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231233, d238938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58177 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d231234 q = 1) (hb : d238939 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231234, d238939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231234, d238939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d231235 q = 1) (hb : d238940 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231235, d238940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d231235, d238940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d231236 q = 1) (hb : d238941 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231236, d238941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d231236, d238941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d231237 q = 1) (hb : d238942 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231237, d238942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d231237, d238942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d231238 q = 1) (hb : d238943 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231238, d238943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231238, d238943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58179 (p : Pattern) (ha : d231244 p = 1) (hb : d238949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231239 q = 1) (hb : d238944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231239, d238944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231239, d238944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58178 q ha hb
  have h2 (q : Pattern) (ha : d231240 q = 1) (hb : d238945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231240, d238945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231240, d238945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231241 q = 1) (hb : d238946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231241, d238946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231241, d238946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231242 q = 1) (hb : d238947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231242, d238947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231242, d238947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231243 q = 1) (hb : d238948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231243, d238948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231243, d238948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231244 q = 1) (hb : d238949 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231244, d238949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231244, d238949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58180 (p : Pattern) (ha : d238020 p = 1) (hb : d238956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29177 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29209 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238016 q = 1) (hb : d238952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238016, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238016, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d29304 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238017 q = 1) (hb : d238953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238017, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238017, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238018 q = 1) (hb : d238954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238018, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238018, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238019 q = 1) (hb : d238955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238019, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238019, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238020 q = 1) (hb : d238956 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238020, d238956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238020, d238956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58181 (p : Pattern) (ha : d238030 p = 1) (hb : d238961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29168 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29177 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238016 q = 1) (hb : d238952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238016, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238016, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d29304 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238017 q = 1) (hb : d238953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238017, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238017, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238018 q = 1) (hb : d238954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238018, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238018, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238019 q = 1) (hb : d238955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238019, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238019, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d29314 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29319 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d29321 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238026 q = 1) (hb : d238957 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238026, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238026, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238027 q = 1) (hb : d238958 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238027, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238027, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d238028 q = 1) (hb : d238959 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238028, d238959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238028, d238959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238029 q = 1) (hb : d238960 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238029, d238960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238029, d238960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d238030 q = 1) (hb : d238961 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238030, d238961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238030, d238961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58182 (p : Pattern) (ha : d238740 p = 1) (hb : d238968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238026 q = 1) (hb : d238957 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238026, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238026, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29328 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238027 q = 1) (hb : d238958 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238027, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238027, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238028 q = 1) (hb : d238966 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238028, d238966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238028, d238966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238029 q = 1) (hb : d238967 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238029, d238967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238029, d238967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238740 q = 1) (hb : d238968 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238740, d238968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238740, d238968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58183 (p : Pattern) (ha : d238751 p = 1) (hb : d238978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29426 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238746 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238747 q = 1) (hb : d238974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238747, d238974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238747, d238974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29496 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238748 q = 1) (hb : d238975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238748, d238975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238748, d238975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238749 q = 1) (hb : d238976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238749, d238976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238749, d238976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238750 q = 1) (hb : d238977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238750, d238977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238750, d238977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238751 q = 1) (hb : d238978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238751, d238978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238751, d238978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58184 (p : Pattern) (ha : d238757 p = 1) (hb : d238984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29160 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238031 q = 1) (hb : d238962 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238031, d238962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58180 q ha hb
    | true =>
      simp only [d238031, d238962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58181 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29346 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238032 q = 1) (hb : d238963 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238032, d238963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238032, d238963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238738 q = 1) (hb : d238964 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238738, d238964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238738, d238964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238739 q = 1) (hb : d238965 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238739, d238965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238739, d238965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238741 q = 1) (hb : d238969 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238741, d238969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238741, d238969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58182 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29355 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238742 q = 1) (hb : d238970 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238742, d238970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238742, d238970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238743 q = 1) (hb : d238971 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238743, d238971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238743, d238971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238744 q = 1) (hb : d238972 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238744, d238972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238744, d238972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238745 q = 1) (hb : d238973 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238745, d238973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238745, d238973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238752 q = 1) (hb : d238979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238752, d238979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238752, d238979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58183 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29512 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238753 q = 1) (hb : d238980 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238753, d238980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238753, d238980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d238754 q = 1) (hb : d238981 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238754, d238981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238754, d238981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238755 q = 1) (hb : d238982 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238755, d238982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238755, d238982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238756 q = 1) (hb : d238983 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238756, d238983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238756, d238983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238757 q = 1) (hb : d238984 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238757, d238984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238757, d238984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58185 (p : Pattern) (ha : d238763 p = 1) (hb : d238990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238758 q = 1) (hb : d238985 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238758, d238985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238758, d238985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58184 q ha hb
  have h2 (q : Pattern) (ha : d238759 q = 1) (hb : d238986 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238759, d238986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238759, d238986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238760 q = 1) (hb : d238987 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238760, d238987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238760, d238987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238761 q = 1) (hb : d238988 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238761, d238988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238761, d238988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238762 q = 1) (hb : d238989 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238762, d238989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238762, d238989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238763 q = 1) (hb : d238990 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238763, d238990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238763, d238990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58186 (p : Pattern) (ha : d238256 p = 1) (hb : d238998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238252 q = 1) (hb : d238994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238252, d238994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238252, d238994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238253 q = 1) (hb : d238995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238253, d238995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238253, d238995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238254 q = 1) (hb : d238996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238254, d238996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238254, d238996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238255 q = 1) (hb : d238997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238255, d238997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238255, d238997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238256 q = 1) (hb : d238998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238256, d238998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238256, d238998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58187 (p : Pattern) (ha : d238266 p = 1) (hb : d239003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238252 q = 1) (hb : d238994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238252, d238994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238252, d238994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238253 q = 1) (hb : d238995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238253, d238995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238253, d238995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238254 q = 1) (hb : d238996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238254, d238996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238254, d238996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238255 q = 1) (hb : d238997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238255, d238997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238255, d238997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d29826 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29831 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238262 q = 1) (hb : d238999 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238262, d238999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238262, d238999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238263 q = 1) (hb : d239000 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238263, d239000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238263, d239000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d238264 q = 1) (hb : d239001 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238264, d239001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238264, d239001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238265 q = 1) (hb : d239002 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238265, d239002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238265, d239002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d238266 q = 1) (hb : d239003 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238266, d239003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238266, d239003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58188 (p : Pattern) (ha : d238769 p = 1) (hb : d239010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238262 q = 1) (hb : d238999 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238262, d238999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238262, d238999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238263 q = 1) (hb : d239000 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238263, d239000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238263, d239000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238264 q = 1) (hb : d239008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238264, d239008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238264, d239008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238265 q = 1) (hb : d239009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238265, d239009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238265, d239009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238769 q = 1) (hb : d239010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238769, d239010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238769, d239010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58189 (p : Pattern) (ha : d238780 p = 1) (hb : d239020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238776 q = 1) (hb : d239016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238776, d239016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238776, d239016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238777 q = 1) (hb : d239017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238777, d239017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238777, d239017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238778 q = 1) (hb : d239018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238778, d239018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238778, d239018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238779 q = 1) (hb : d239019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238779, d239019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238779, d239019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238780 q = 1) (hb : d239020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238780, d239020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238780, d239020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58190 (p : Pattern) (ha : d238786 p = 1) (hb : d239026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29641 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238267 q = 1) (hb : d239004 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238267, d239004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58186 q ha hb
    | true =>
      simp only [d238267, d239004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58187 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238268 q = 1) (hb : d239005 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238268, d239005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238268, d239005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238767 q = 1) (hb : d239006 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238767, d239006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238767, d239006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238768 q = 1) (hb : d239007 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238768, d239007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238768, d239007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238770 q = 1) (hb : d239011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238770, d239011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238770, d239011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58188 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29867 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238771 q = 1) (hb : d239012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238771, d239012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238771, d239012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238772 q = 1) (hb : d239013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238772, d239013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238772, d239013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238773 q = 1) (hb : d239014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238773, d239014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238773, d239014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238774 q = 1) (hb : d239015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238774, d239015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238774, d239015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238781 q = 1) (hb : d239021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238781, d239021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238781, d239021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58189 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238782 q = 1) (hb : d239022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238782, d239022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238782, d239022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d238783 q = 1) (hb : d239023 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238783, d239023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238783, d239023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238784 q = 1) (hb : d239024 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238784, d239024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238784, d239024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238785 q = 1) (hb : d239025 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238785, d239025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238785, d239025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238786 q = 1) (hb : d239026 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238786, d239026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238786, d239026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58191 (p : Pattern) (ha : d238792 p = 1) (hb : d239032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238787 q = 1) (hb : d239027 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238787, d239027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238787, d239027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58190 q ha hb
  have h2 (q : Pattern) (ha : d238788 q = 1) (hb : d239028 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238788, d239028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238788, d239028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238789 q = 1) (hb : d239029 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238789, d239029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238789, d239029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238790 q = 1) (hb : d239030 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238790, d239030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238790, d239030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238791 q = 1) (hb : d239031 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238791, d239031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238791, d239031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238792 q = 1) (hb : d239032 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238792, d239032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238792, d239032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58192 (p : Pattern) (ha : d238480 p = 1) (hb : d239041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30188 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30197 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30221 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238476 q = 1) (hb : d239037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238476, d239037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238476, d239037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30343 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238477 q = 1) (hb : d239038 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238477, d239038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238477, d239038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238478 q = 1) (hb : d239039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238478, d239039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238478, d239039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238479 q = 1) (hb : d239040 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238479, d239040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238479, d239040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238480 q = 1) (hb : d239041 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238480, d239041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238480, d239041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro58193 (p : Pattern) (ha : d238490 p = 1) (hb : d239046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30221 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238476 q = 1) (hb : d239037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238476, d239037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238476, d239037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30343 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238477 q = 1) (hb : d239038 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238477, d239038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238477, d239038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238478 q = 1) (hb : d239039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238478, d239039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238478, d239039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238479 q = 1) (hb : d239040 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238479, d239040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238479, d239040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30353 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30358 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30360 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238486 q = 1) (hb : d239042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238486, d239042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238486, d239042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30367 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238487 q = 1) (hb : d239043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238487, d239043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238487, d239043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d238488 q = 1) (hb : d239044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238488, d239044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238488, d239044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238489 q = 1) (hb : d239045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238489, d239045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238489, d239045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d238490 q = 1) (hb : d239046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238490, d239046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238490, d239046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58194 (p : Pattern) (ha : d238799 p = 1) (hb : d239053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238486 q = 1) (hb : d239042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238486, d239042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238486, d239042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238487 q = 1) (hb : d239043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238487, d239043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238487, d239043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238488 q = 1) (hb : d239051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238488, d239051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238488, d239051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238489 q = 1) (hb : d239052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238489, d239052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238489, d239052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238799 q = 1) (hb : d239053 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238799, d239053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238799, d239053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58195 (p : Pattern) (ha : d238810 p = 1) (hb : d239063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30474 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238805 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238806 q = 1) (hb : d239059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238806, d239059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238806, d239059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30559 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238807 q = 1) (hb : d239060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238807, d239060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238807, d239060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238808 q = 1) (hb : d239061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238808, d239061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238808, d239061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238809 q = 1) (hb : d239062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238809, d239062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238809, d239062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238810 q = 1) (hb : d239063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238810, d239063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238810, d239063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58196 (p : Pattern) (ha : d238816 p = 1) (hb : d239069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30180 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238491 q = 1) (hb : d239047 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238491, d239047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58192 q ha hb
    | true =>
      simp only [d238491, d239047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58193 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30385 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238492 q = 1) (hb : d239048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238492, d239048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238492, d239048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238797 q = 1) (hb : d239049 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238797, d239049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238797, d239049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238798 q = 1) (hb : d239050 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238798, d239050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238798, d239050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238800 q = 1) (hb : d239054 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238800, d239054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238800, d239054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58194 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d30394 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238801 q = 1) (hb : d239055 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238801, d239055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238801, d239055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238802 q = 1) (hb : d239056 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238802, d239056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238802, d239056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238803 q = 1) (hb : d239057 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238803, d239057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238803, d239057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238804 q = 1) (hb : d239058 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238804, d239058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238804, d239058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238811 q = 1) (hb : d239064 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238811, d239064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238811, d239064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58195 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30575 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238812 q = 1) (hb : d239065 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238812, d239065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238812, d239065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d238813 q = 1) (hb : d239066 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238813, d239066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238813, d239066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238814 q = 1) (hb : d239067 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238814, d239067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238814, d239067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238815 q = 1) (hb : d239068 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238815, d239068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238815, d239068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238816 q = 1) (hb : d239069 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238816, d239069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238816, d239069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro58197 (p : Pattern) (ha : d238822 p = 1) (hb : d239075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238817 q = 1) (hb : d239070 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238817, d239070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238817, d239070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58196 q ha hb
  have h2 (q : Pattern) (ha : d238818 q = 1) (hb : d239071 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238818, d239071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238818, d239071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238819 q = 1) (hb : d239072 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238819, d239072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238819, d239072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238820 q = 1) (hb : d239073 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238820, d239073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238820, d239073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238821 q = 1) (hb : d239074 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238821, d239074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238821, d239074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238822 q = 1) (hb : d239075 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238822, d239075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238822, d239075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58198 (p : Pattern) (ha : d238828 p = 1) (hb : d239081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d231218 q = 1) (hb : d238910 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231218, d238910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58167 q hb ha
    | true =>
      simp only [d231218, d238910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58173 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231245 q = 1) (hb : d238950 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231245, d238950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231245, d238950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58179 q ha hb
  have h3 (q : Pattern) (ha : d231246 q = 1) (hb : d238951 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231246, d238951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231246, d238951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238764 q = 1) (hb : d238991 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238764, d238991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238764, d238991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58185 q ha hb
  have h5 (q : Pattern) (ha : d238765 q = 1) (hb : d238992 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d238765, d238992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238765, d238992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238766 q = 1) (hb : d238993 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d238766, d238993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238766, d238993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238793 q = 1) (hb : d239033 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238793, d239033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238793, d239033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58191 q ha hb
  have h8 (q : Pattern) (ha : d238794 q = 1) (hb : d239034 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d238794, d239034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238794, d239034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238795 q = 1) (hb : d239035 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d238795, d239035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238795, d239035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238796 q = 1) (hb : d239036 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d238796, d239036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238796, d239036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d238823 q = 1) (hb : d239076 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238823, d239076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238823, d239076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58197 q ha hb
  have h12 (q : Pattern) (ha : d238824 q = 1) (hb : d239077 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d238824, d239077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238824, d239077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238825 q = 1) (hb : d239078 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d238825, d239078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238825, d239078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238826 q = 1) (hb : d239079 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d238826, d239079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238826, d239079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238827 q = 1) (hb : d239080 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d238827, d239080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238827, d239080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d238828 q = 1) (hb : d239081 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d238828, d239081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238828, d239081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro58199 (p : Pattern) (ha : d238834 p = 1) (hb : d239087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238829 q = 1) (hb : d239082 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d238829, d239082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58198 q ha hb
    | true =>
      simp only [d238829, d239082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d238830 q = 1) (hb : d239083 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d238830, d239083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238830, d239083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d238831 q = 1) (hb : d239084 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d238831, d239084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238831, d239084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d238832 q = 1) (hb : d239085 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d238832, d239085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238832, d239085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238833 q = 1) (hb : d239086 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d238833, d239086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238833, d239086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d238834 q = 1) (hb : d239087 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d238834, d239087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238834, d239087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58200 (p : Pattern) (ha : d238840 p = 1) (hb : d239093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238835 q = 1) (hb : d239088 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d238835, d239088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58199 q ha hb
    | true =>
      simp only [d238835, d239088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d238836 q = 1) (hb : d239089 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d238836, d239089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238836, d239089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d238837 q = 1) (hb : d239090 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d238837, d239090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238837, d239090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d238838 q = 1) (hb : d239091 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d238838, d239091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238838, d239091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238839 q = 1) (hb : d239092 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d238839, d239092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238839, d239092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d238840 q = 1) (hb : d239093 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d238840, d239093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238840, d239093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58201 (p : Pattern) (ha : d238846 p = 1) (hb : d239099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238841 q = 1) (hb : d239094 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d238841, d239094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58200 q ha hb
    | true =>
      simp only [d238841, d239094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d238842 q = 1) (hb : d239095 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d238842, d239095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238842, d239095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d238843 q = 1) (hb : d239096 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d238843, d239096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238843, d239096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d238844 q = 1) (hb : d239097 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d238844, d239097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238844, d239097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238845 q = 1) (hb : d239098 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d238845, d239098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238845, d239098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d238846 q = 1) (hb : d239099 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d238846, d239099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238846, d239099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58202 (p : Pattern) (ha : d238852 p = 1) (hb : d239105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238847 q = 1) (hb : d239100 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d238847, d239100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58201 q ha hb
    | true =>
      simp only [d238847, d239100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d238848 q = 1) (hb : d239101 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d238848, d239101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238848, d239101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d238849 q = 1) (hb : d239102 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d238849, d239102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238849, d239102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d238850 q = 1) (hb : d239103 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d238850, d239103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238850, d239103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238851 q = 1) (hb : d239104 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d238851, d239104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238851, d239104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d238852 q = 1) (hb : d239105 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d238852, d239105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238852, d239105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58203 (p : Pattern) (ha : d238858 p = 1) (hb : d239111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238853 q = 1) (hb : d239106 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d238853, d239106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58202 q ha hb
    | true =>
      simp only [d238853, d239106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d238854 q = 1) (hb : d239107 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d238854, d239107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238854, d239107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d238855 q = 1) (hb : d239108 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d238855, d239108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238855, d239108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d238856 q = 1) (hb : d239109 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d238856, d239109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238856, d239109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238857 q = 1) (hb : d239110 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d238857, d239110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238857, d239110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d238858 q = 1) (hb : d239111 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d238858, d239111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238858, d239111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58204 (p : Pattern) (ha : d238864 p = 1) (hb : d239117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238859 q = 1) (hb : d239112 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d238859, d239112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58203 q ha hb
    | true =>
      simp only [d238859, d239112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d238860 q = 1) (hb : d239113 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d238860, d239113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238860, d239113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d238861 q = 1) (hb : d239114 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d238861, d239114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238861, d239114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d238862 q = 1) (hb : d239115 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d238862, d239115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238862, d239115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238863 q = 1) (hb : d239116 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d238863, d239116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238863, d239116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d238864 q = 1) (hb : d239117 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d238864, d239117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238864, d239117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58205 (p : Pattern) (ha : d238870 p = 1) (hb : d239123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238865 q = 1) (hb : d239118 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d238865, d239118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58204 q ha hb
    | true =>
      simp only [d238865, d239118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d238866 q = 1) (hb : d239119 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d238866, d239119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238866, d239119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d238867 q = 1) (hb : d239120 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d238867, d239120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238867, d239120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d238868 q = 1) (hb : d239121 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d238868, d239121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238868, d239121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238869 q = 1) (hb : d239122 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d238869, d239122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238869, d239122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d238870 q = 1) (hb : d239123 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d238870, d239123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238870, d239123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58206 (p : Pattern) (ha : d23931 p = 1) (hb : d236582 p = 1) : d23694 p = 1 := by
  have h0 (q : Pattern) (ha : d823 q = 1) (hb : d236581 q = 1) : d823 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d530 q = 1) : d530 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1087 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1088 q = 1) (hb : d236581 q = 1) : d531 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d236581, d531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1088, d236581, d531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1089 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1089, d532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1090 q = 1) (hb : d236581 q = 1) : d824 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1090, d824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23927 q = 1) (hb : d236582 q = 1) : d23692 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23927, d236582, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23927, d236582, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d23928 q = 1) (hb : d236582 q = 1) : d23693 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23928, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23928, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1093 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1094 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d1094, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d1095 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1095, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d1096 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1096, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23929 q = 1) (hb : d236582 q = 1) : d23419 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23929, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23929, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d23930 q = 1) (hb : d236582 q = 1) : d23420 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23930, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23930, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h18 (q : Pattern) (ha : d23931 q = 1) (hb : d236582 q = 1) : d23694 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23931, d23694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23931, d23694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro58207 (p : Pattern) (ha : d23938 p = 1) (hb : d236582 p = 1) : d23421 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d530 q = 1) : d530 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1087 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1088 q = 1) (hb : d236581 q = 1) : d531 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d236581, d531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1088, d236581, d531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1089 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1089, d532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1093 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1094 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1094, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1095 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1095, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1096 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1096, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d23929 q = 1) (hb : d236582 q = 1) : d23419 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23929, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23929, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23930 q = 1) (hb : d236582 q = 1) : d23420 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23930, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23930, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d132 q = 1) : d132 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1104 q = 1) (hb : d236581 q = 1) : d133 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d1105 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d1106 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1106, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23936 q = 1) (hb : d236582 q = 1) : d23228 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23936, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23936, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h20 (q : Pattern) (ha : d23937 q = 1) (hb : d236582 q = 1) : d23229 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23937, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23937, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h21 (q : Pattern) (ha : d23938 q = 1) (hb : d236582 q = 1) : d23421 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23938, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23938, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58208 (p : Pattern) (ha : d23944 p = 1) (hb : d236582 p = 1) : d237981 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1094 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1094, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1095 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1095, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d132 q = 1) : d132 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1104 q = 1) (hb : d236581 q = 1) : d133 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1105 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1106 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1106, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d23936 q = 1) (hb : d236582 q = 1) : d23228 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23936, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23936, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d23937 q = 1) (hb : d236582 q = 1) : d23229 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23937, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23937, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1115 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h16 (q : Pattern) (ha : d1116 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d20 q = 1) (hb : d236581 q = 1) : d20 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1117 q = 1) (hb : d236581 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5537 q = 1) (hb : d236582 q = 1) : d205892 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5537, d236582, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5537, d236582, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h20 (q : Pattern) (ha : d5538 q = 1) (hb : d236582 q = 1) : d205893 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5538, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5538, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h21 (q : Pattern) (ha : d23944 q = 1) (hb : d236582 q = 1) : d237981 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23944, d237981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23944, d237981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58209 (p : Pattern) (ha : d23950 p = 1) (hb : d236582 p = 1) : d237987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23932 q = 1) (hb : d236582 q = 1) : d23695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58206 q ha hb
    | true =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23933 q = 1) (hb : d236582 q = 1) : d23696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23934 q = 1) (hb : d236582 q = 1) : d23697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23934, d23697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23934, d23697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23935 q = 1) (hb : d236582 q = 1) : d23698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23935, d23698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23935, d23698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23939 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
    | true =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23940 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23941 q = 1) (hb : d236582 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23942 q = 1) (hb : d236582 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23943 q = 1) (hb : d236582 q = 1) : d23699 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23943, d23699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23943, d23699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23945 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
    | true =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23946 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23947 q = 1) (hb : d236582 q = 1) : d237984 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23948 q = 1) (hb : d236582 q = 1) : d237985 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23949 q = 1) (hb : d236582 q = 1) : d237986 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23949, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23950 q = 1) (hb : d236582 q = 1) : d237987 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23950, d237987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23950, d237987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58210 (p : Pattern) (ha : d23952 p = 1) (hb : d236582 p = 1) : d237989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23939 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
    | true =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23940 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23941 q = 1) (hb : d236582 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23942 q = 1) (hb : d236582 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23945 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
    | true =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23946 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23947 q = 1) (hb : d236582 q = 1) : d237984 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23948 q = 1) (hb : d236582 q = 1) : d237985 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23949 q = 1) (hb : d236582 q = 1) : d237986 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23949, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23951 q = 1) (hb : d236582 q = 1) : d237988 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23951, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23952 q = 1) (hb : d236582 q = 1) : d237989 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23952, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23952, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58211 (p : Pattern) (ha : d23956 p = 1) (hb : d236582 p = 1) : d237993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23945 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
    | true =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23946 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23947 q = 1) (hb : d236582 q = 1) : d237984 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23948 q = 1) (hb : d236582 q = 1) : d237985 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23951 q = 1) (hb : d236582 q = 1) : d237988 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23951, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23951, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1136 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57593 q ha hb
    | true =>
      simp only [d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1137 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1138 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1139 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1140 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23956 q = 1) (hb : d236582 q = 1) : d237993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23956, d237993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23956, d237993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58212 (p : Pattern) (ha : d23963 p = 1) (hb : d236582 p = 1) : d238000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23953 q = 1) (hb : d236582 q = 1) : d237990 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58209 q ha hb
    | true =>
      simp only [d23953, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58210 q ha hb
  have h2 (q : Pattern) (ha : d23954 q = 1) (hb : d236582 q = 1) : d237991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23955 q = 1) (hb : d236582 q = 1) : d237992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23957 q = 1) (hb : d236582 q = 1) : d237994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58210 q ha hb
    | true =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58211 q ha hb
  have h5 (q : Pattern) (ha : d23958 q = 1) (hb : d236582 q = 1) : d237995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23959 q = 1) (hb : d236582 q = 1) : d237996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23960 q = 1) (hb : d236582 q = 1) : d237997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23960, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23961 q = 1) (hb : d236582 q = 1) : d237998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23961, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23962 q = 1) (hb : d236582 q = 1) : d237999 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23962, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23962, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23963 q = 1) (hb : d236582 q = 1) : d238000 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23963, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23963, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro58213 (p : Pattern) (ha : d23967 p = 1) (hb : d236582 p = 1) : d238004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23957 q = 1) (hb : d236582 q = 1) : d237994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58210 q ha hb
    | true =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58211 q ha hb
  have h2 (q : Pattern) (ha : d23958 q = 1) (hb : d236582 q = 1) : d237995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23959 q = 1) (hb : d236582 q = 1) : d237996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23961 q = 1) (hb : d236582 q = 1) : d237998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23961, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23961, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23966 q = 1) (hb : d236582 q = 1) : d238003 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23966, d238003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23966, d238003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23967 q = 1) (hb : d236582 q = 1) : d238004 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23967, d238004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23967, d238004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58214 (p : Pattern) (ha : d23973 p = 1) (hb : d236582 p = 1) : d238010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d236582 q = 1) : d238007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d236582 q = 1) : d238008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d236582 q = 1) : d238009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23973 q = 1) (hb : d236582 q = 1) : d238010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23973, d238010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23973, d238010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58215 (p : Pattern) (ha : d23977 p = 1) (hb : d236582 p = 1) : d238014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d236582 q = 1) : d238011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d236582 q = 1) : d238012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23976 q = 1) (hb : d236582 q = 1) : d238013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23976, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23976, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23977 q = 1) (hb : d236582 q = 1) : d238014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23977, d238014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23977, d238014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58216 (p : Pattern) (ha : d23983 p = 1) (hb : d236582 p = 1) : d238020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d236582 q = 1) : d238015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58214 q ha hb
    | true =>
      simp only [d23978, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58215 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d236582 q = 1) : d238016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d236582 q = 1) : d238017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d236582 q = 1) : d238018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d236582 q = 1) : d238019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23983 q = 1) (hb : d236582 q = 1) : d238020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23983, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23983, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58217 (p : Pattern) (ha : d23986 p = 1) (hb : d236582 p = 1) : d238023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d236582 q = 1) : d238007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d236582 q = 1) : d238008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23972 q = 1) (hb : d236582 q = 1) : d238009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23972, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23972, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23986 q = 1) (hb : d236582 q = 1) : d238023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23986, d238023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23986, d238023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58218 (p : Pattern) (ha : d23987 p = 1) (hb : d236582 p = 1) : d238024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d236582 q = 1) : d238011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d236582 q = 1) : d238012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23976 q = 1) (hb : d236582 q = 1) : d238013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23976, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23976, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23987 q = 1) (hb : d236582 q = 1) : d238024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23987, d238024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23987, d238024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58219 (p : Pattern) (ha : d23993 p = 1) (hb : d236582 p = 1) : d238030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d236582 q = 1) : d238015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58214 q ha hb
    | true =>
      simp only [d23978, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58215 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d236582 q = 1) : d238016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d236582 q = 1) : d238017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d236582 q = 1) : d238018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d236582 q = 1) : d238019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23988 q = 1) (hb : d236582 q = 1) : d238025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58217 q ha hb
    | true =>
      simp only [d23988, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58218 q ha hb
  have h7 (q : Pattern) (ha : d23989 q = 1) (hb : d236582 q = 1) : d238026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23989, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23990 q = 1) (hb : d236582 q = 1) : d238027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23990, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23991 q = 1) (hb : d236582 q = 1) : d238028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23992 q = 1) (hb : d236582 q = 1) : d238029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23993 q = 1) (hb : d236582 q = 1) : d238030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d23993, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23993, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58220 (p : Pattern) (ha : d24140 p = 1) (hb : d236582 p = 1) : d238109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23978 q = 1) (hb : d236582 q = 1) : d238015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23978, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58214 q ha hb
    | true =>
      simp only [d23978, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58215 q ha hb
  have h2 (q : Pattern) (ha : d23979 q = 1) (hb : d236582 q = 1) : d238016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23979, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23979, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23980 q = 1) (hb : d236582 q = 1) : d238017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23980, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23980, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23981 q = 1) (hb : d236582 q = 1) : d238018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23981, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23981, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23982 q = 1) (hb : d236582 q = 1) : d238019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23982, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23982, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24135 q = 1) (hb : d236582 q = 1) : d238104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24135, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58215 q ha hb
    | true =>
      simp only [d24135, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24136 q = 1) (hb : d236582 q = 1) : d238105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24136, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24136, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24137 q = 1) (hb : d236582 q = 1) : d238106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24137, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24137, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24138 q = 1) (hb : d236582 q = 1) : d238107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24138, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24138, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24139 q = 1) (hb : d236582 q = 1) : d238108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24139, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24139, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24140 q = 1) (hb : d236582 q = 1) : d238109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24140, d238109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24140, d238109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58221 (p : Pattern) (ha : d24146 p = 1) (hb : d236582 p = 1) : d238115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24135 q = 1) (hb : d236582 q = 1) : d238104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24135, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58215 q ha hb
    | true =>
      simp only [d24135, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24136 q = 1) (hb : d236582 q = 1) : d238105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24136, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24136, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24137 q = 1) (hb : d236582 q = 1) : d238106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24137, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24137, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24138 q = 1) (hb : d236582 q = 1) : d238107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24138, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24138, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24139 q = 1) (hb : d236582 q = 1) : d238108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24139, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24139, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24141 q = 1) (hb : d236582 q = 1) : d238110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24141, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58218 q ha hb
    | true =>
      simp only [d24141, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24142 q = 1) (hb : d236582 q = 1) : d238111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24142, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24142, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24143 q = 1) (hb : d236582 q = 1) : d238112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24143, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24143, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24144 q = 1) (hb : d236582 q = 1) : d238113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24144, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24144, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24145 q = 1) (hb : d236582 q = 1) : d238114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24145, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24145, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24146 q = 1) (hb : d236582 q = 1) : d238115 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24146, d238115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24146, d238115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro58222 (p : Pattern) (ha : d24155 p = 1) (hb : d236582 p = 1) : d238124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24141 q = 1) (hb : d236582 q = 1) : d238110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24141, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58218 q ha hb
    | true =>
      simp only [d24141, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24142 q = 1) (hb : d236582 q = 1) : d238111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24142, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24142, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24143 q = 1) (hb : d236582 q = 1) : d238112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24143, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24143, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24144 q = 1) (hb : d236582 q = 1) : d238113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24144, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24144, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24145 q = 1) (hb : d236582 q = 1) : d238114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24145, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24145, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24155 q = 1) (hb : d236582 q = 1) : d238124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24155, d238124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24155, d238124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58223 (p : Pattern) (ha : d24186 p = 1) (hb : d236582 p = 1) : d238146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24170 q = 1) (hb : d236582 q = 1) : d23534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
  have h2 (q : Pattern) (ha : d23939 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
    | true =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24171 q = 1) (hb : d236582 q = 1) : d23535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24171, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23940 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24172 q = 1) (hb : d236582 q = 1) : d23536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24172, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24173 q = 1) (hb : d236582 q = 1) : d23537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24173, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24176 q = 1) (hb : d236582 q = 1) : d238136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
  have h8 (q : Pattern) (ha : d23945 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
    | true =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24177 q = 1) (hb : d236582 q = 1) : d238137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24177, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23946 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24178 q = 1) (hb : d236582 q = 1) : d238138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24178, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24179 q = 1) (hb : d236582 q = 1) : d238139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24179, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24180 q = 1) (hb : d236582 q = 1) : d238140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24180, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24180, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24185 q = 1) (hb : d236582 q = 1) : d238145 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24185, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24185, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24186 q = 1) (hb : d236582 q = 1) : d238146 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24186, d238146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24186, d238146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58224 (p : Pattern) (ha : d24191 p = 1) (hb : d236582 p = 1) : d238151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24176 q = 1) (hb : d236582 q = 1) : d238136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
  have h2 (q : Pattern) (ha : d23945 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
    | true =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24177 q = 1) (hb : d236582 q = 1) : d238137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24177, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23946 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24178 q = 1) (hb : d236582 q = 1) : d238138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24178, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24179 q = 1) (hb : d236582 q = 1) : d238139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24179, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24185 q = 1) (hb : d236582 q = 1) : d238145 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24185, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24185, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1406 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57593 q ha hb
  have h9 (q : Pattern) (ha : d1136 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57593 q ha hb
    | true =>
      simp only [d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1407 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1137 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1408 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1409 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1410 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24191 q = 1) (hb : d236582 q = 1) : d238151 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24191, d238151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24191, d238151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58225 (p : Pattern) (ha : d24210 p = 1) (hb : d236582 p = 1) : d238170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24192 q = 1) (hb : d236582 q = 1) : d238152 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24192, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58223 q ha hb
    | true =>
      simp only [d24192, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58224 q ha hb
  have h2 (q : Pattern) (ha : d24193 q = 1) (hb : d236582 q = 1) : d238153 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24193, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24193, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24194 q = 1) (hb : d236582 q = 1) : d238154 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24194, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24194, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24200 q = 1) (hb : d236582 q = 1) : d238160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24200, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24200, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24209 q = 1) (hb : d236582 q = 1) : d238169 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24209, d238169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24209, d238169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24210 q = 1) (hb : d236582 q = 1) : d238170 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24210, d238170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24210, d238170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58226 (p : Pattern) (ha : d24285 p = 1) (hb : d236582 p = 1) : d238193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24211 q = 1) (hb : d236582 q = 1) : d238171 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24211, d238171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58225 q ha hb
    | true =>
      simp only [d24211, d238171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24212 q = 1) (hb : d236582 q = 1) : d238172 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24212, d238172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24212, d238172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24282 q = 1) (hb : d236582 q = 1) : d238190 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24282, d238190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24282, d238190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24283 q = 1) (hb : d236582 q = 1) : d238191 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24283, d238191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24283, d238191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24284 q = 1) (hb : d236582 q = 1) : d238192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24284, d238192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24284, d238192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24285 q = 1) (hb : d236582 q = 1) : d238193 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24285, d238193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24285, d238193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58227 (p : Pattern) (ha : d24291 p = 1) (hb : d236582 p = 1) : d238199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24286 q = 1) (hb : d236582 q = 1) : d238194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24286, d238194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58226 q ha hb
    | true =>
      simp only [d24286, d238194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24287 q = 1) (hb : d236582 q = 1) : d238195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24287, d238195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24287, d238195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24288 q = 1) (hb : d236582 q = 1) : d238196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24288, d238196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24288, d238196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24289 q = 1) (hb : d236582 q = 1) : d238197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24289, d238197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24289, d238197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24290 q = 1) (hb : d236582 q = 1) : d238198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24290, d238198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24290, d238198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24291 q = 1) (hb : d236582 q = 1) : d238199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d24291, d238199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24291, d238199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58228 (p : Pattern) (ha : d23998 p = 1) (hb : d236582 p = 1) : d238035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d236582 q = 1) : d238007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d236582 q = 1) : d238008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23997 q = 1) (hb : d236582 q = 1) : d238034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23997, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23997, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23998 q = 1) (hb : d236582 q = 1) : d238035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23998, d238035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23998, d238035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58229 (p : Pattern) (ha : d24000 p = 1) (hb : d236582 p = 1) : d238037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d236582 q = 1) : d238011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d236582 q = 1) : d238012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23999 q = 1) (hb : d236582 q = 1) : d238036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23999, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23999, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24000 q = 1) (hb : d236582 q = 1) : d238037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24000, d238037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24000, d238037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58230 (p : Pattern) (ha : d24007 p = 1) (hb : d236582 p = 1) : d238044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d236582 q = 1) : d238007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24005 q = 1) (hb : d236582 q = 1) : d238042 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24005, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24005, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24006 q = 1) (hb : d236582 q = 1) : d238043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24006, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24006, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24007 q = 1) (hb : d236582 q = 1) : d238044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24007, d238044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24007, d238044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58231 (p : Pattern) (ha : d24010 p = 1) (hb : d236582 p = 1) : d238047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d236582 q = 1) : d238011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24008 q = 1) (hb : d236582 q = 1) : d238045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24008, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24008, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24009 q = 1) (hb : d236582 q = 1) : d238046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24009, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24009, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24010 q = 1) (hb : d236582 q = 1) : d238047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24010, d238047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24010, d238047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58232 (p : Pattern) (ha : d24016 p = 1) (hb : d236582 p = 1) : d238051 p = 1 := by
  have h0 (q : Pattern) (ha : d24015 q = 1) (hb : d236582 q = 1) : d24015 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d823 q = 1) (hb : d236581 q = 1) : d823 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d530 q = 1) : d530 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1087 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1088 q = 1) (hb : d236581 q = 1) : d531 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d236581, d531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1088, d236581, d531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1089 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1089, d532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1090 q = 1) (hb : d236581 q = 1) : d824 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1090, d824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23927 q = 1) (hb : d236582 q = 1) : d23692 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23927, d236582, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23927, d236582, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d23928 q = 1) (hb : d236582 q = 1) : d23693 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23928, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23928, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24016 q = 1) (hb : d236582 q = 1) : d238051 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24016, d238051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24016, d238051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro58233 (p : Pattern) (ha : d24022 p = 1) (hb : d236582 p = 1) : d238057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24017 q = 1) (hb : d236582 q = 1) : d238052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24017, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58232 q ha hb
    | true =>
      simp only [d24017, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24018 q = 1) (hb : d236582 q = 1) : d238053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24018, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24018, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24019 q = 1) (hb : d236582 q = 1) : d238054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24019, d238054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24019, d238054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24020 q = 1) (hb : d236582 q = 1) : d238055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24020, d238055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24020, d238055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23932 q = 1) (hb : d236582 q = 1) : d23695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58206 q ha hb
    | true =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23933 q = 1) (hb : d236582 q = 1) : d23696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23934 q = 1) (hb : d236582 q = 1) : d23697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23934, d23697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23934, d23697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23935 q = 1) (hb : d236582 q = 1) : d23698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23935, d23698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23935, d23698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24021 q = 1) (hb : d236582 q = 1) : d238056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24021, d238056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24021, d238056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23939 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
    | true =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23940 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23941 q = 1) (hb : d236582 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23942 q = 1) (hb : d236582 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23943 q = 1) (hb : d236582 q = 1) : d23699 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23943, d23699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23943, d23699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24022 q = 1) (hb : d236582 q = 1) : d238057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24022, d238057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24022, d238057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58234 (p : Pattern) (ha : d24028 p = 1) (hb : d236582 p = 1) : d238063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24023 q = 1) (hb : d236582 q = 1) : d238058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24023, d238058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58233 q ha hb
    | true =>
      simp only [d24023, d238058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58209 q ha hb
  have h2 (q : Pattern) (ha : d24024 q = 1) (hb : d236582 q = 1) : d238059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24024, d238059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24024, d238059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24025 q = 1) (hb : d236582 q = 1) : d238060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24025, d238060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24025, d238060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23953 q = 1) (hb : d236582 q = 1) : d237990 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58209 q ha hb
    | true =>
      simp only [d23953, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58210 q ha hb
  have h5 (q : Pattern) (ha : d23954 q = 1) (hb : d236582 q = 1) : d237991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23955 q = 1) (hb : d236582 q = 1) : d237992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24026 q = 1) (hb : d236582 q = 1) : d238061 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24026, d238061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24026, d238061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23957 q = 1) (hb : d236582 q = 1) : d237994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58210 q ha hb
    | true =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58211 q ha hb
  have h9 (q : Pattern) (ha : d23958 q = 1) (hb : d236582 q = 1) : d237995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23959 q = 1) (hb : d236582 q = 1) : d237996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23960 q = 1) (hb : d236582 q = 1) : d237997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23960, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24027 q = 1) (hb : d236582 q = 1) : d238062 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24027, d238062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24027, d238062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24028 q = 1) (hb : d236582 q = 1) : d238063 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24028, d238063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24028, d238063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58235 (p : Pattern) (ha : d24034 p = 1) (hb : d236582 p = 1) : d238069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24029 q = 1) (hb : d236582 q = 1) : d238064 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24029, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58234 q ha hb
    | true =>
      simp only [d24029, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24030 q = 1) (hb : d236582 q = 1) : d238065 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24030, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24030, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24031 q = 1) (hb : d236582 q = 1) : d238066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24031, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24031, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24032 q = 1) (hb : d236582 q = 1) : d238067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24032, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24032, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24033 q = 1) (hb : d236582 q = 1) : d238068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24033, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24033, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24034 q = 1) (hb : d236582 q = 1) : d238069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24034, d238069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24034, d238069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58236 (p : Pattern) (ha : d24091 p = 1) (hb : d236582 p = 1) : d237989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23939 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
    | true =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23940 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23941 q = 1) (hb : d236582 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23941, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23942 q = 1) (hb : d236582 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23942, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23945 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
    | true =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23946 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23947 q = 1) (hb : d236582 q = 1) : d237984 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23947, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23948 q = 1) (hb : d236582 q = 1) : d237985 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23948, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23949 q = 1) (hb : d236582 q = 1) : d237986 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23949, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23949, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5540 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57619 q ha hb
    | true =>
      simp only [d5540, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5541 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5541, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5542 q = 1) (hb : d236582 q = 1) : d237984 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5542, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5543 q = 1) (hb : d236582 q = 1) : d237985 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5543, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5544 q = 1) (hb : d236582 q = 1) : d237988 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5544, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d24091 q = 1) (hb : d236582 q = 1) : d237989 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24091, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24091, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58237 (p : Pattern) (ha : d24097 p = 1) (hb : d236582 p = 1) : d238000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23953 q = 1) (hb : d236582 q = 1) : d237990 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23953, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58209 q ha hb
    | true =>
      simp only [d23953, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58210 q ha hb
  have h2 (q : Pattern) (ha : d23954 q = 1) (hb : d236582 q = 1) : d237991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23954, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23954, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23955 q = 1) (hb : d236582 q = 1) : d237992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23955, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23955, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23957 q = 1) (hb : d236582 q = 1) : d237994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58210 q ha hb
    | true =>
      simp only [d23957, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58211 q ha hb
  have h5 (q : Pattern) (ha : d23958 q = 1) (hb : d236582 q = 1) : d237995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23958, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23959 q = 1) (hb : d236582 q = 1) : d237996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23959, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23960 q = 1) (hb : d236582 q = 1) : d237997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23960, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23960, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24092 q = 1) (hb : d236582 q = 1) : d237994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d24092, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58236 q ha hb
    | true =>
      simp only [d24092, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57621 q ha hb
  have h9 (q : Pattern) (ha : d24093 q = 1) (hb : d236582 q = 1) : d237995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d24093, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24093, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d24094 q = 1) (hb : d236582 q = 1) : d237996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d24094, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24094, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d24095 q = 1) (hb : d236582 q = 1) : d237998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d24095, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24095, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d24096 q = 1) (hb : d236582 q = 1) : d237999 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d24096, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24096, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d24097 q = 1) (hb : d236582 q = 1) : d238000 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d24097, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24097, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro58238 (p : Pattern) (ha : d24103 p = 1) (hb : d236582 p = 1) : d238075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24098 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24098, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58237 q ha hb
    | true =>
      simp only [d24098, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24099 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24099, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24099, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24100 q = 1) (hb : d236582 q = 1) : d238072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24100, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24100, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24101 q = 1) (hb : d236582 q = 1) : d238073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24101, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24101, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24102 q = 1) (hb : d236582 q = 1) : d238074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24102, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24102, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24103 q = 1) (hb : d236582 q = 1) : d238075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24103, d238075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24103, d238075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro58239 (p : Pattern) (ha : d211244 p = 1) (hb : d236582 p = 1) : d238081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24001 q = 1) (hb : d236582 q = 1) : d238038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24001, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58228 q ha hb
    | true =>
      simp only [d24001, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58229 q ha hb
  have h2 (q : Pattern) (ha : d24002 q = 1) (hb : d236582 q = 1) : d238039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24002, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24002, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24003 q = 1) (hb : d236582 q = 1) : d238040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24003, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24003, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24004 q = 1) (hb : d236582 q = 1) : d238041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24004, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24004, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24011 q = 1) (hb : d236582 q = 1) : d238048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24011, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58230 q ha hb
    | true =>
      simp only [d24011, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58231 q ha hb
  have h6 (q : Pattern) (ha : d24012 q = 1) (hb : d236582 q = 1) : d238049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24012, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24012, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24013 q = 1) (hb : d236582 q = 1) : d238050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24013, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24013, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24035 q = 1) (hb : d236582 q = 1) : d238070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24035, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58235 q ha hb
    | true =>
      simp only [d24035, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58214 q ha hb
  have h9 (q : Pattern) (ha : d211240 q = 1) (hb : d236582 q = 1) : d238071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211240, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d24104 q = 1) (hb : d236582 q = 1) : d238076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24104, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58238 q ha hb
    | true =>
      simp only [d24104, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24105 q = 1) (hb : d236582 q = 1) : d238077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24105, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24105, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d211241 q = 1) (hb : d236582 q = 1) : d238078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211241, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211242 q = 1) (hb : d236582 q = 1) : d238079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211242, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211243 q = 1) (hb : d236582 q = 1) : d238080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211243, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211244 q = 1) (hb : d236582 q = 1) : d238081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211244, d238081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211244, d238081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro58240 (p : Pattern) (ha : d24110 p = 1) (hb : d236582 p = 1) : d238082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d236582 q = 1) : d238007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23971 q = 1) (hb : d236582 q = 1) : d238008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23971, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23997 q = 1) (hb : d236582 q = 1) : d238034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23997, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23997, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24110 q = 1) (hb : d236582 q = 1) : d238082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24110, d238082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24110, d238082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58241 (p : Pattern) (ha : d24111 p = 1) (hb : d236582 p = 1) : d238083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d236582 q = 1) : d238011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23975 q = 1) (hb : d236582 q = 1) : d238012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23975, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23999 q = 1) (hb : d236582 q = 1) : d238036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23999, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23999, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24111 q = 1) (hb : d236582 q = 1) : d238083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24111, d238083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24111, d238083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58242 (p : Pattern) (ha : d24116 p = 1) (hb : d236582 p = 1) : d238088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23970 q = 1) (hb : d236582 q = 1) : d238007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23970, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24005 q = 1) (hb : d236582 q = 1) : d238042 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24005, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24005, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24006 q = 1) (hb : d236582 q = 1) : d238043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24006, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24006, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24116 q = 1) (hb : d236582 q = 1) : d238088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24116, d238088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24116, d238088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58243 (p : Pattern) (ha : d24117 p = 1) (hb : d236582 p = 1) : d238089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23968 q = 1) (hb : d236582 q = 1) : d238005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58213 q ha hb
    | true =>
      simp only [d23968, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23969 q = 1) (hb : d236582 q = 1) : d238006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23969, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23974 q = 1) (hb : d236582 q = 1) : d238011 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23974, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24008 q = 1) (hb : d236582 q = 1) : d238045 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24008, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24008, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24009 q = 1) (hb : d236582 q = 1) : d238046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24009, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24009, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24117 q = 1) (hb : d236582 q = 1) : d238089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24117, d238089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24117, d238089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58244 (p : Pattern) (ha : d24121 p = 1) (hb : d236582 p = 1) : d238093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24029 q = 1) (hb : d236582 q = 1) : d238064 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24029, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58234 q ha hb
    | true =>
      simp only [d24029, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24030 q = 1) (hb : d236582 q = 1) : d238065 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24030, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24030, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23964 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58212 q ha hb
    | true =>
      simp only [d23964, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23965 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23965, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24031 q = 1) (hb : d236582 q = 1) : d238066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24031, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24031, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24032 q = 1) (hb : d236582 q = 1) : d238067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24032, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24032, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24033 q = 1) (hb : d236582 q = 1) : d238068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24033, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24033, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24121 q = 1) (hb : d236582 q = 1) : d238093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24121, d238093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24121, d238093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro58245 (p : Pattern) (ha : d24127 p = 1) (hb : d236582 p = 1) : d238096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24098 q = 1) (hb : d236582 q = 1) : d238001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d24098, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58237 q ha hb
    | true =>
      simp only [d24098, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d24099 q = 1) (hb : d236582 q = 1) : d238002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d24099, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24099, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24100 q = 1) (hb : d236582 q = 1) : d238072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d24100, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24100, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24101 q = 1) (hb : d236582 q = 1) : d238073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d24101, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24101, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24102 q = 1) (hb : d236582 q = 1) : d238074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d24102, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d24102, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24127 q = 1) (hb : d236582 q = 1) : d238096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d24127, d238096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24127, d238096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro58246 (p : Pattern) (ha : d211249 p = 1) (hb : d236582 p = 1) : d238102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24001 q = 1) (hb : d236582 q = 1) : d238038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24001, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58228 q ha hb
    | true =>
      simp only [d24001, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58229 q ha hb
  have h2 (q : Pattern) (ha : d24002 q = 1) (hb : d236582 q = 1) : d238039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24002, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24002, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24003 q = 1) (hb : d236582 q = 1) : d238040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24003, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24003, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24004 q = 1) (hb : d236582 q = 1) : d238041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24004, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24004, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24011 q = 1) (hb : d236582 q = 1) : d238048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24011, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58230 q ha hb
    | true =>
      simp only [d24011, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58231 q ha hb
  have h6 (q : Pattern) (ha : d24012 q = 1) (hb : d236582 q = 1) : d238049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24012, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24012, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24013 q = 1) (hb : d236582 q = 1) : d238050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24013, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24013, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d24035 q = 1) (hb : d236582 q = 1) : d238070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24035, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58235 q ha hb
    | true =>
      simp only [d24035, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58214 q ha hb
  have h9 (q : Pattern) (ha : d211240 q = 1) (hb : d236582 q = 1) : d238071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211240, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d24104 q = 1) (hb : d236582 q = 1) : d238076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24104, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58238 q ha hb
    | true =>
      simp only [d24104, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24105 q = 1) (hb : d236582 q = 1) : d238077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24105, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d24105, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d211241 q = 1) (hb : d236582 q = 1) : d238078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211241, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211242 q = 1) (hb : d236582 q = 1) : d238079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211242, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211243 q = 1) (hb : d236582 q = 1) : d238080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211243, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d24112 q = 1) (hb : d236582 q = 1) : d238084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24112, d238084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58240 q ha hb
    | true =>
      simp only [d24112, d238084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58241 q ha hb
  have h16 (q : Pattern) (ha : d24113 q = 1) (hb : d236582 q = 1) : d238085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24113, d238085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24113, d238085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d24114 q = 1) (hb : d236582 q = 1) : d238086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24114, d238086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24114, d238086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24115 q = 1) (hb : d236582 q = 1) : d238087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24115, d238087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24115, d238087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24118 q = 1) (hb : d236582 q = 1) : d238090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24118, d238090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58242 q ha hb
    | true =>
      simp only [d24118, d238090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58243 q ha hb
  have h20 (q : Pattern) (ha : d24119 q = 1) (hb : d236582 q = 1) : d238091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24119, d238091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24119, d238091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24120 q = 1) (hb : d236582 q = 1) : d238092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24120, d238092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d24120, d238092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d24122 q = 1) (hb : d236582 q = 1) : d238094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24122, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58244 q ha hb
    | true =>
      simp only [d24122, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58217 q ha hb
  have h23 (q : Pattern) (ha : d211245 q = 1) (hb : d236582 q = 1) : d238095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d211245, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d24128 q = 1) (hb : d236582 q = 1) : d238097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24128, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58245 q ha hb
    | true =>
      simp only [d24128, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d24129 q = 1) (hb : d236582 q = 1) : d238098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24129, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d24129, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d211246 q = 1) (hb : d236582 q = 1) : d238099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d211246, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d211247 q = 1) (hb : d236582 q = 1) : d238100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211247, d238100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d211247, d238100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d211248 q = 1) (hb : d236582 q = 1) : d238101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211248, d238101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d211248, d238101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d211249 q = 1) (hb : d236582 q = 1) : d238102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211249, d238102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d211249, d238102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro58247 (p : Pattern) (ha : d211256 p = 1) (hb : d236582 p = 1) : d238122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24122 q = 1) (hb : d236582 q = 1) : d238094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24122, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58244 q ha hb
    | true =>
      simp only [d24122, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58217 q ha hb
  have h2 (q : Pattern) (ha : d211245 q = 1) (hb : d236582 q = 1) : d238095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211245, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24128 q = 1) (hb : d236582 q = 1) : d238097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24128, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58245 q ha hb
    | true =>
      simp only [d24128, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24129 q = 1) (hb : d236582 q = 1) : d238098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24129, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24129, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211246 q = 1) (hb : d236582 q = 1) : d238099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211246, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211254 q = 1) (hb : d236582 q = 1) : d238120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211254, d238120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211254, d238120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211255 q = 1) (hb : d236582 q = 1) : d238121 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211255, d238121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211255, d238121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211256 q = 1) (hb : d236582 q = 1) : d238122 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211256, d238122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211256, d238122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro58248 (p : Pattern) (ha : d24175 p = 1) (hb : d236582 p = 1) : d238135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24161 q = 1) (hb : d236582 q = 1) : d238130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24161, d238130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24161, d238130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58232 q ha hb
  have h2 (q : Pattern) (ha : d24017 q = 1) (hb : d236582 q = 1) : d238052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24017, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58232 q ha hb
    | true =>
      simp only [d24017, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24162 q = 1) (hb : d236582 q = 1) : d238131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24162, d238131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24162, d238131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d24018 q = 1) (hb : d236582 q = 1) : d238053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24018, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24018, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24163 q = 1) (hb : d236582 q = 1) : d238132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24163, d238132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24163, d238132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24164 q = 1) (hb : d236582 q = 1) : d238133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24164, d238133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24164, d238133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24165 q = 1) (hb : d236582 q = 1) : d23814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24165, d23814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24165, d23814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58206 q ha hb
  have h8 (q : Pattern) (ha : d23932 q = 1) (hb : d236582 q = 1) : d23695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58206 q ha hb
    | true =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24166 q = 1) (hb : d236582 q = 1) : d23815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24166, d23815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24166, d23815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23933 q = 1) (hb : d236582 q = 1) : d23696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24167 q = 1) (hb : d236582 q = 1) : d23816 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24167, d23816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24167, d23816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24168 q = 1) (hb : d236582 q = 1) : d23817 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24168, d23817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24168, d23817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24169 q = 1) (hb : d236582 q = 1) : d238134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24169, d238134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24169, d238134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24170 q = 1) (hb : d236582 q = 1) : d23534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
  have h15 (q : Pattern) (ha : d23939 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
    | true =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24171 q = 1) (hb : d236582 q = 1) : d23535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24171, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23940 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24172 q = 1) (hb : d236582 q = 1) : d23536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24172, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24173 q = 1) (hb : d236582 q = 1) : d23537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24173, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24174 q = 1) (hb : d236582 q = 1) : d23818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24174, d23818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24174, d23818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24175 q = 1) (hb : d236582 q = 1) : d238135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24175, d238135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24175, d238135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro58249 (p : Pattern) (ha : d24181 p = 1) (hb : d236582 p = 1) : d238141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24165 q = 1) (hb : d236582 q = 1) : d23814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24165, d23814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24165, d23814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58206 q ha hb
  have h2 (q : Pattern) (ha : d23932 q = 1) (hb : d236582 q = 1) : d23695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58206 q ha hb
    | true =>
      simp only [d23932, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d24166 q = 1) (hb : d236582 q = 1) : d23815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24166, d23815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24166, d23815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23933 q = 1) (hb : d236582 q = 1) : d23696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23933, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d24167 q = 1) (hb : d236582 q = 1) : d23816 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24167, d23816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24167, d23816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24168 q = 1) (hb : d236582 q = 1) : d23817 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24168, d23817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24168, d23817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d24170 q = 1) (hb : d236582 q = 1) : d23534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24170, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24170, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
  have h8 (q : Pattern) (ha : d23939 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58207 q ha hb
    | true =>
      simp only [d23939, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d24171 q = 1) (hb : d236582 q = 1) : d23535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24171, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24171, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23940 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23940, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d24172 q = 1) (hb : d236582 q = 1) : d23536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24172, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d24172, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d24173 q = 1) (hb : d236582 q = 1) : d23537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24173, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d24173, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d24174 q = 1) (hb : d236582 q = 1) : d23818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24174, d23818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24174, d23818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d24176 q = 1) (hb : d236582 q = 1) : d238136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d24176, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24176, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
  have h15 (q : Pattern) (ha : d23945 q = 1) (hb : d236582 q = 1) : d237982 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro58208 q ha hb
    | true =>
      simp only [d23945, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d24177 q = 1) (hb : d236582 q = 1) : d238137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d24177, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d24177, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23946 q = 1) (hb : d236582 q = 1) : d237983 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23946, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d24178 q = 1) (hb : d236582 q = 1) : d238138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d24178, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d24178, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d24179 q = 1) (hb : d236582 q = 1) : d238139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d24179, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d24179, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d24180 q = 1) (hb : d236582 q = 1) : d238140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d24180, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d24180, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d24181 q = 1) (hb : d236582 q = 1) : d238141 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d24181, d238141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d24181, d238141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
end NetHack.Soko22Hazard87
